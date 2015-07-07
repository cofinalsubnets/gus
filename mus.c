#include <stdarg.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>

typedef enum {
  t_pair,
  t_func,
  t_form,
  t_prim,
  t_num,
  t_sym,
  t_str,
  t_err,
  t_err_thrown,
  t_nil
} t_t;

typedef struct _val {
  union _data {
    struct {
      struct _val *fst;
      struct _val *snd;
    } pair;
    struct _val* (*prim)(struct _val*);
    long num;
    char *str;
  } data;
  struct _val *next;
  t_t type;
  char alive;
} *val;

void print(val, FILE*);
void println(val, FILE*);

#define nil NULL
#define car(c) ((c)->data.pair.fst)
#define cdr(c) ((c)->data.pair.snd)
#define caar(c) car(car(c))
#define cadr(c) car(cdr(c))
#define cdar(c) cdr(car(c))
#define cddr(c) cdr(cdr(c))
#define type_of(x) (x ? x->type : t_nil)
#define GC_ALLOC_CYCLE (1<<15)
#define GC_MEM_MAX (1<<25)
#define MARKED 1
#define ATOMIC (1<<2)
#define IS(f,h) (h&&(h->alive&f))
#define SET(f,h) if(f)h->alive|=f
#define UNSET(f,h) if(f)h->alive&=~f

char gc_atomic = 0;
unsigned long gc_allocs = 0, gc_mem = 0;
struct _val root = { { { NULL, NULL } }, NULL, t_pair, 0 };
val vals = &root;

void gc_mark(val v) {
  if (!v || IS(MARKED, v)) return;
  SET(MARKED, v);
  t_t t = type_of(v);
  if (t == t_pair || t == t_func || t == t_form) {
    gc_mark(car(v));
    gc_mark(cdr(v));
  }
}

void gc() {
  gc_mark(&root);
  for (val prev = NULL, v = vals; v;) {
    if (v->alive) {
      UNSET(MARKED, v);
      prev = v;
      v = v->next;
    } else {
      if (prev) prev->next = v->next;
      else vals = v->next;
      t_t t = type_of(v);
      if (t == t_str || t == t_err || t == t_err_thrown) free(v->data.str);
      gc_mem -= sizeof(struct _val);
      free(v);
      v = prev ? prev->next : vals;
    }
  }
  gc_allocs = 0;
}

val new(t_t t) {
  if (gc_mem + sizeof(struct _val) > GC_MEM_MAX) {
    gc();
    if (gc_mem + sizeof(struct _val) > GC_MEM_MAX) goto oom;
  }
  if (++gc_allocs >= GC_ALLOC_CYCLE) gc();

  val v = (val) malloc(sizeof(struct _val));
  if (!v) goto oom;

  gc_mem += sizeof(struct _val);
  v->alive = gc_atomic;
  v->next = vals;
  v->type = t;
  vals = v;
  memset(&(v->data), 0, sizeof(union _data));
  return v;
oom:
  fprintf(stderr, "oom!\n");
  abort();
}

void gc_atomic_begin() { gc_atomic = ATOMIC; }
void gc_atomic_end() {
  gc_atomic = 0;
  for (val v = vals; v && IS(ATOMIC, v); v = v->next) UNSET(ATOMIC, v);
}

#define STACK car(workspace)
#define RET_VAL cadr(workspace)
#define GLOBAL cddr(workspace)
#define SYMBOL_TABLE root.data.pair.snd
val t, sym_eval, sym_apply, sym_if, sym_def, sym_set, sym_fn, sym_rw, sym_qt,
    (*special_preinit(val))(val, val), (*special_postinit(val))(val, val),
    (*(*special)(val))(val, val) = special_preinit, _car(val), _cdr(val),
    eval(val, val), eval_args(val, val, val*), zip(val, val), assq_c(val, val),
    spec_if(val, val), spec_def(val, val), spec_set(val, val), workspace,
    spec_lambda(val, val), spec_form(val, val), spec_quote(val, val),
    _eval(val), _apply(val);

#define ctor1(t, s, v) { val r = new(t); r->data.s = v; return r; }
#define ctor2(t, a, b) { val r = new(t); car(r) = a; cdr(r) = b; return r; }
val cons(val car, val cdr)   ctor2(t_pair, car, cdr)
val lambda(val def, val env) ctor2(t_func, def, env)
val form(val def, val env)   ctor2(t_form, def, env)
val string(char *s)          ctor1(t_str, str, strdup(s))
val num(long l)              ctor1(t_num, num, l)
val prim(val (*p)(val))      ctor1(t_prim, prim, p)
val error(char *s)           ctor1(t_err_thrown, str, strdup(s))
val symbol(char *s) {
  for (val st = SYMBOL_TABLE; st; st = cdr(st))
    if (!strcmp(car(st)->data.str, s)) return car(st);
  SYMBOL_TABLE = cons(nil, SYMBOL_TABLE);
  val v = new(t_sym);
  v->data.str = strdup(s);
  car(SYMBOL_TABLE) = v;
  return v;
}

#define RETURN(x) { RET_VAL=x; pop_frame(); return; }
#define CONTINUE(s, a, b) { caar(STACK) = s; car(cdar(STACK)) = nil; cadr(cdar(STACK)) = a; cddr(cdar(STACK)) = b; return; }
#define require(v, t) if (type_of(v) != t) return error("Type error: not " #t)
#define pop_frame() STACK = cdr(STACK)
void do_eval(), do_apply();
void push_frame(val frame_type, val a,  val b) {
  STACK = cons(nil, STACK);
  car(STACK) = cons(a, b);
  car(STACK) = cons(nil, car(STACK));
  car(STACK) = cons(frame_type, car(STACK));
}

val return_to(val caller) {
  while (STACK != caller) {
    if (type_of(RET_VAL) == t_err_thrown) pop_frame();
    else if (caar(STACK) == sym_eval) do_eval();
    else do_apply();
  }
  if (type_of(RET_VAL) == t_err_thrown) RET_VAL->type = t_err;
  return RET_VAL;
}

void do_eval() {
  val ev = cdar(STACK), d = cadr(ev), env = cddr(ev);
  val args, acc, fn, (*spec)(val, val);
  if (!env) RETURN(d);
  switch (type_of(d)) {
    case t_pair:
      args = cdr(d);
      if ((spec = special(car(d)))) RETURN(spec(cdr(d), env));
      car(ev) = acc = cons(nil, nil);
      fn = car(acc) = eval(car(d), env);
      t_t tp = type_of(fn);
      if (tp == t_form) {
        push_frame(sym_apply, fn, args);
        CONTINUE(sym_eval, return_to(cdr(STACK)), env);
      }
      if (fn == t || fn == nil || tp == t_prim || tp == t_func) {
        args = eval_args(args, env, &cdr(acc));
        if (fn == t) RETURN(_car(args));
        if (fn == nil) RETURN(_cdr(args));
        if (tp == t_prim) RETURN(fn->data.prim(args));
        CONTINUE(sym_apply, fn, args);
      }
      RETURN(error("Type error: not applicable"));
    case t_sym:
      for (; env; env = cdr(env))
        if ((acc = assq_c(d, car(env)))) RETURN(cdr(acc));
      RETURN(error("Reference error: not defined"));
    default:
      RETURN(d);
  }
}

void do_apply() {
  val ev = cdar(STACK), fn = cadr(ev), args = cddr(ev);
  gc_atomic_begin(); /* FIXME: this shouldn't rely on gc_atomic */
  val body = cdar(fn), env = car(ev) = cons(zip(caar(fn), args), cdr(fn));
  gc_atomic_end();
  for (; cdr(body); body = cdr(body)) eval(car(body), env);
  CONTINUE(sym_eval, car(body), env);
}

#define eval_toplevel(v) eval(v, GLOBAL)
val eval(val d, val env) {
  push_frame(sym_eval, d, env);
  return return_to(cdr(STACK));
}

val zip(val a, val b) {
  if (type_of(a) != t_pair || type_of(b) != t_pair) return nil;
  return cons(cons(car(a), car(b)), zip(cdr(a), cdr(b)));
}

val eval_args(val l, val env, val *acc) {
  if (!l || l->type != t_pair) return l;
  val tl = eval_args(cdr(l), env, acc); /* safe from gc b/c stored in acc */
  val hd = eval(car(l), env); /* safe from gc b/c stored in RET_VAL */
  return *acc = cons(hd, tl);
}

struct { val k; val (*fn)(val, val); } forms[] = {
  { NULL, spec_if },
  { NULL, spec_def },
  { NULL, spec_set },
  { NULL, spec_lambda },
  { NULL, spec_form },
  { NULL, spec_quote }
};

val (*special_preinit(val k))(val, val) {
  val vs[] = { sym_if, sym_def, sym_set, sym_fn, sym_rw, sym_qt };
  for (int i = 0; i < sizeof(vs) / sizeof(*vs); ++i) forms[i].k = vs[i];
  return (special = special_postinit)(k);
}

val (*special_postinit(val k))(val, val) {
  for (int i = 0; i < (sizeof(forms) / sizeof(*forms)); ++i)
    if (forms[i].k == k) return forms[i].fn;
  return nil;
}

#define require_binary(args) require(args, t_pair); require(cdr(args), t_pair); require(cddr(args), t_nil)
val spec_if(val b, val env) {
  if (!car(b) || !cadr(b) || !car(cddr(b)) || cdr(cddr(b)))
    return error("syntax error: if");
  return eval(eval(car(b), env) ? cadr(b) : car(cddr(b)), env);
}

val spec_def(val b, val env) {
  require_binary(b);
  val k = car(b), x = cadr(b);
  require(k, t_sym);
  cdar(env) = cons(caar(env), cdar(env));
  caar(env) = cons(k, nil);
  cdr(caar(env)) = eval(x, env);
  return cdr(caar(env));
}

val spec_set(val b, val env) {
  require_binary(b);
  val kv, k = car(b);
  require(k, t_sym);
  if ((kv = assq_c(k, env))) cdr(kv) = eval(cadr(b), env);
  return cdr(kv);
}

val spec_lambda(val b, val env) {
  require(b, t_pair);
  require(cdr(b), t_pair);
  return lambda(b, env);
}

val spec_form(val b, val env) {
  require(b, t_pair);
  require(cdr(b), t_pair);
  return form(b, env);
}

val spec_quote(val v, val env) { require(cdr(v), t_nil); return car(v); }

#define BINARY(as) require_binary(as); val a = car(as), b = cadr(as)
#define binop(n, tp, r) val n(val as) { BINARY(as); require(a, tp); require(b, tp); return r; }
#define binop_n(n, op) binop(n, t_num, num(a->data.num op b->data.num))
binop_n(_add, +) binop_n(_sub, -) binop_n(_mul, *) binop_n(_div, /)
binop(_lt, t_num, a->data.num < b->data.num ? t : nil)
binop(_gt, t_num, a->data.num > b->data.num ? t : nil)
val _cons(val as) { BINARY(as); return cons(a, b); }
val _and(val as) { BINARY(as); return a && b ? a : nil; }
val _or(val as) { BINARY(as); return a ? a : b; }
val scurry(val n) { require(n, t_nil); exit(0); }
val set_hd(val as) { BINARY(as); require(a, t_pair); return car(a) = b; }
val set_tl(val as) { BINARY(as); require(a, t_pair); return cdr(a) = b; }
val assq(val), eq(val), eqish(val);
#define unop(n, t, fn) val n(val as) { require(cdr(as), t_nil); require(car(as), t); return fn(car(as)); }
unop(_car, t_pair, car) unop(_cdr, t_pair, cdr)
val _eval(val v) { require(cdr(v), t_nil); return eval_toplevel(car(v)); }
val _apply(val v) { BINARY(v); return eval_toplevel(cons(a, b)); }

void initialize() {
  gc_atomic_begin();
  val global = cons(cons(symbol("eq?"), prim(eq)), nil);
  root.data.pair.fst = workspace = cons(nil, cons(nil, cons(global, nil)));

  struct { val *s; char *n; } syms[] = {
    { &sym_eval, "eval" },
    { &sym_apply, "apply" },
    { &t, "t" },
    { &sym_if, "if" },
    { &sym_def, "def" },
    { &sym_set, "set" },
    { &sym_fn, "fn" },
    { &sym_rw, "rw" },
    { &sym_qt, "qt" }
  };

  for (int i = 0; i < sizeof(syms)/sizeof(*syms); i++)
    *syms[i].s = symbol(syms[i].n);

  struct { char *s; val (*p)(val); } prims[] = {
    { "assq", assq },
    { "+", _add },
    { "-", _sub },
    { "*", _mul },
    { "/", _div },
    { "hd", _car },
    { "tl", _cdr },
    { ":", _cons },
    { "scurry", scurry },
    { "<", _lt },
    { ">", _gt },
    { "and", _and },
    { "or", _or },
    { "set-hd", set_hd },
    { "set-tl", set_tl },
    { "=", eqish },
    { "eval", _eval },
    { "apply", _apply }
  };

  for (int i = 0; i < sizeof(prims)/sizeof(*prims); i++) {
    cdr(global) = cons(car(global), cdr(global));
    car(global) = cons(symbol(prims[i].s), prim(prims[i].p));
  }

  gc_atomic_end();
}

val eq_c(val a, val b) { return a == b ? t : nil; }
val eq(val args) { require_binary(args); return eq_c(car(args), cadr(args)); }
val assq(val args) { require_binary(args); return assq_c(car(args), cadr(args)); }
val assq_c(val key, val alist) {
  for (; type_of(alist) == t_pair; alist = cdr(alist))
    if (eq_c(caar(alist), key)) return car(alist);
  return nil;
}

#define EQ_ON(c) (a->data.c == b->data.c ? t : nil)
val eqish(val v) {
  BINARY(v);
  if (eq_c(a, b)) return t;
  if (type_of(a) != type_of(b)) return nil;
  switch (type_of(a)) {
    case t_str:  return strcmp(a->data.str, b->data.str) ? nil : t;
    case t_num:  return EQ_ON(num);
    case t_prim: return EQ_ON(prim);
    default:     return nil;
  }
}

val read_num(char**), read_sym(char**), read_str(char**), read_cons(char**);
val read_val(char **str) {
  while (isspace(**str)) ++(*str);
  char c = **str;
  if (!c) return nil;
  if (c == '\'' || c == '(' || c == '"') {
    ++(*str);
    return c == '\'' ? cons(sym_qt, cons(read_val(str), nil)) :
           c == '(' ? read_cons(str) :
           read_str(str);
  }
  val d = read_num(str);
  return d ? d : read_sym(str);
}

val read_num(char **str) {
  char *end = NULL;
  long n = strtol(*str, &end, 10);
  if (*str == end) return NULL;
  *str = end;
  return num(n);
}

val read_sym(char **str) {
  char buf[100];
  memset(buf, 0, 100);
  sscanf(*str, "%99[^( \n\t\v\r\f)\"']", buf);
  *str += strlen(buf);
  return symbol(buf);
}

val read_str(char **str) {
  char *start = *str;
  while (**str && **str != '"') {
    if (**str == '\\') ++(*str);
    ++(*str);
  }
  val s = new(t_str);
  s->data.str = strndup(start, *str - start); 
  return s;
}

val read_cons(char **str) {
  while (isspace(**str)) ++(*str);
  char c = **str;
  if (!c || c == ')' || c == '.') {
    ++(*str);
    return c == '.' ? read_val(str) : nil;
  }
  val v = read_val(str);
  return cons(v, read_cons(str));
}

val read(char **str) {
  gc_atomic_begin();
  val v = read_val(str);
  gc_atomic_end();
  return v;
}

void println(val d, FILE *f) { print(d, f); putc('\n', f); }
void print(val d, FILE *f) {
  switch (type_of(d)) {
    case t_nil:  fprintf(f, "()"); break;
    case t_num:  fprintf(f, "%ld", d->data.num); break;
    case t_prim:
    case t_func: fputs("<fn>", f); break;
    case t_form: fputs("<rw>", f); break;
    case t_err:
    case t_err_thrown:
    case t_sym:  fputs(d->data.str, f); break;
    case t_str:
      putc('"', f);
      for (char *c = d->data.str; *c; c++)
        *c == '"' ? fprintf(f, "\\\"") : putc(*c, f);
      putc('"', f);
      break;
    case t_pair:
      putc('(', f);
      print(car(d), f);
      for (d = cdr(d); type_of(d) == t_pair; d = cdr(d)) {
        putc(' ', f);
        print(car(d), f);
      }
      if (d) {
        fprintf(f, " . ");
        print(d, f);
      }
      putc(')', f);
  }
}

void repl() {
  char buf[100], *b = buf;
  printf(">> ");
  while ((b = fgets(buf, 100, stdin))) {
    val v = eval_toplevel(read(&b));
    printf("=> ");
    println(v, stdout);
    printf(">> ");
  }
  puts("(scurry)");
}

int main() {
  initialize();
  repl();
  return 0;
}
