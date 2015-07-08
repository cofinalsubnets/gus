#include <stdarg.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <setjmp.h>
#include "lib.h"

typedef enum { t_pair, t_fn, t_rw, t_prim, t_num, t_sym, t_str, t_nil } t_t;

typedef struct _val {
  union _data {
    struct {
      struct _val *fst;
      struct _val *snd;
    } pair;
    struct {
      struct _val* (*fn)(struct _val*);
      char *name;
    } prim;
    long num;
    char *str;
  } data;
  struct _val *next;
  t_t type;
  char alive;
} *val;

void print(val, FILE*);
void println(val, FILE*);
val read(char **str);
void panic(int);

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
struct _val root = { { { nil, nil } }, NULL, t_pair, 0 };
val vals = &root;

void gc_mark(val v) {
  if (!v || IS(MARKED, v)) return;
  SET(MARKED, v);
  t_t t = type_of(v);
  if (t == t_pair || t == t_fn || t == t_rw) {
    gc_mark(car(v));
    gc_mark(cdr(v));
  }
}

void gc() {
  gc_mark(&root);
  for (val prev = NULL, v = vals; v;)
    if (v->alive) {
      UNSET(MARKED, v);
      prev = v;
      v = v->next;
    } else {
      prev ? (prev->next = v->next) : (vals = v->next);
      t_t t = type_of(v);
      if (t == t_str) free(v->data.str);
      gc_mem -= sizeof(struct _val);
      free(v);
      v = (prev ? prev->next : vals);
    }
}

val new(t_t t) {
  if (gc_mem + sizeof(struct _val) > GC_MEM_MAX) gc();
  if (gc_mem + sizeof(struct _val) > GC_MEM_MAX) goto oom;
  if ((++gc_allocs) % GC_ALLOC_CYCLE == 0) gc();

  val v = (val) malloc(sizeof(struct _val));
  if (!v) goto oom;
  gc_mem += sizeof(struct _val);
  v->alive = gc_atomic, v->next = vals, v->type = t;
  memset(&(v->data), 0, sizeof(union _data));
  return vals = v;
oom:
  fprintf(stderr, "Out of memory after %lu allocations.\n", gc_allocs);
  exit(1);
}

void gc_atomic_begin() { gc_atomic = ATOMIC; }
void gc_atomic_end() {
  gc_atomic = 0;
  for (val v = vals; v && IS(ATOMIC, v); v = v->next) UNSET(ATOMIC, v);
}

#define STACK root.data.pair.fst
#define RET_VAL car(root.data.pair.snd)
#define GLOBAL cadr(root.data.pair.snd)
#define SYMBOL_TABLE cddr(root.data.pair.snd)
val t, sym_if, sym_def, sym_set, sym_fn, sym_rw, sym_qt, sym_qq, sym_uq,
    sym_xq, _eval(val), _apply(val),
    (*special_preinit(val))(val, val), (*special_postinit(val))(val, val),
    (*(*special)(val))(val, val) = special_preinit, _car(val), _cdr(val),
    eval(val, val), eval_args(val, val, val*), assq_c(val, val);

#define ctor1(t, s, v) { val r = new(t); r->data.s = v; return r; }
#define ctor2(t, a, b) { val r = new(t); car(r) = a; cdr(r) = b; return r; }
val cons(val car, val cdr)   ctor2(t_pair, car, cdr)
val lambda(val def, val env) ctor2(t_fn, def, env)
val form(val def, val env)   ctor2(t_rw, def, env)
val string(char *s)          ctor1(t_str, str, strdup(s))
val num(long l)              ctor1(t_num, num, l)
val prim(val (*f)(val), char *n) {
  val p = new(t_prim);
  p->data.prim.fn = f, p->data.prim.name = n;
  return p;
}
val symbol(char *s) {
  for (val st = SYMBOL_TABLE; st; st = cdr(st))
    if (!strcmp(car(st)->data.str, s)) return car(st);
  SYMBOL_TABLE = cons(nil, SYMBOL_TABLE);
  val v = new(t_sym);
  v->data.str = strdup(s);
  car(SYMBOL_TABLE) = v;
  return v;
}

#define STACK_LIMIT 10000
#define RETURN(x) { RET_VAL=x; STACK = cdr(STACK); stack_height--; return; }
#define CONTINUE(s, a, b) { caar(STACK) = s; car(cdar(STACK)) = nil; cadr(cdar(STACK)) = a; cddr(cdar(STACK)) = b; return; }
#define require(v, t) if (type_of(v) != t) return nil
void do_eval(), do_apply();
unsigned long stack_height = 0;
val dbind(val, val, val);
void push_frame(val frame_type, val a,  val b) {
  if (++stack_height > STACK_LIMIT) {
    fputs("stack overflow", stderr);
    panic(1);
  }
  STACK = cons(nil, STACK);
  car(STACK) = cons(a, b);
  car(STACK) = cons(nil, car(STACK));
  car(STACK) = cons(frame_type, car(STACK));
}

val return_to(val caller) {
  while (STACK != caller) caar(STACK) ? do_eval() : do_apply();
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
      if (tp == t_rw) {
        push_frame(nil, fn, args);
        d = return_to(cdr(STACK));
        CONTINUE(t, d, env);
      }
      if (fn == t || fn == nil || tp == t_prim || tp == t_fn) {
        args = eval_args(args, env, &cdr(acc));
        if (fn == t) RETURN(_car(args));
        if (fn == nil) RETURN(_cdr(args));
        if (tp == t_prim) RETURN(fn->data.prim.fn(args));
        CONTINUE(nil, fn, args);
      }
      fprintf(stderr, "error: not applicable: ");
      println(d, stderr);
      panic(1);
    case t_sym:
      for (; env; env = cdr(env))
        if ((acc = assq_c(d, car(env)))) RETURN(cdr(acc));
      fprintf(stderr, "error: not defined: ");
      println(d, stderr);
      panic(1);
    default:
      RETURN(d);
  }
}

void do_apply() {
  val ev = cdar(STACK), fn = cadr(ev), args = cddr(ev);
  gc_atomic_begin(); /* FIXME: this shouldn't rely on gc_atomic */
  val body = cdar(fn), env = car(ev) = cons(dbind(caar(fn), args, fn), cdr(fn));
  gc_atomic_end();
  for (; cdr(body); body = cdr(body)) eval(car(body), env);
  CONTINUE(t, car(body), env);
}

#define eval_toplevel(v) eval(v, cons(GLOBAL, nil))
val eval(val d, val env) {
  push_frame(t, d, env);
  return return_to(cdr(STACK));
}

val append(val a, val b) {
  return !a ? b : !b ? a : cons(car(a), append(cdr(a), b));
}

val dbind(val a, val b, val f) {
  t_t ta = type_of(a), tb = type_of(b);
  if (!a && !b) return nil;
  if (ta == t_pair && tb == ta)
    return append(dbind(car(a), car(b), f), dbind(cdr(a), cdr(b), f));
  if (ta == t_pair || !a) {
    fprintf(stderr, "error: ");
    print(a, stderr);
    fprintf(stderr, " </- ");
    print(b, stderr);
    fprintf(stderr, ": ");
    println(f, stderr);
    panic(1);
  }
  return cons(cons(a, b), nil);
}

val eval_args(val l, val env, val *acc) {
  if (!l || l->type != t_pair) return l;
  val tl = eval_args(cdr(l), env, acc); /* safe from gc b/c stored in acc */
  val hd = eval(car(l), env); /* safe from gc b/c stored in RET_VAL */
  return *acc = cons(hd, tl);
}

int len(val v) { return type_of(v) == t_pair ? 1 + len(cdr(v)) : 0; }
#define arity(l, xs, s) if (len(xs) != l) { fputs(s, stderr); panic(1); }
val spec_if(val b, val env) {
  arity(3, b, "error: syntax: if\n");
  return eval(eval(car(b), env) ? cadr(b) : car(cddr(b)), env);
}

val spec_set(val b, val env) {
  arity(2, b, "error: syntax: set\n");
  val kv, k = car(b);
  require(k, t_sym);
  for (; env; env = cdr(env)) if ((kv = assq_c(k, car(env))))
    return cdr(kv) = eval(cadr(b), env);
  return nil;
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

val spec_quote(val v, val env) {
  require(cdr(v), t_nil);
  return car(v);
}

val spec_def(val b, val env) {
  const char *err = "error: syntax: def\n";
  if (type_of(car(b)) == t_sym) {
    arity(2, b, err);
    val k = car(b), x = cadr(b);
    cdar(env) = cons(caar(env), cdar(env));
    caar(env) = cons(k, nil);
    return cdr(caar(env)) = eval(x, env);
  } else if (type_of(car(b)) == t_pair && type_of(caar(b)) == t_sym) {
    cdar(env) = cons(caar(env), cdar(env));
    caar(env) = cons(caar(b), nil);
    return cdr(caar(env)) = spec_lambda(cons(cdar(b), cdr(b)), env);
  } else {
    fprintf(stderr, err);
    panic(1);
    return nil;
  }
}

val do_xq(val, val, val);
val do_qq(val v, val env) {
  if (type_of(v) != t_pair || car(v) == sym_qq) return v;
  else if (car(v) == sym_uq) return eval(cadr(v), env);
  else if (type_of(car(v)) == t_pair && caar(v) == sym_xq)
    return do_xq(eval(car(cdar(v)), env), cdr(v), env);
  else return cons(do_qq(car(v), env), do_qq(cdr(v), env));
}

val do_xq(val a, val d, val env) {
  return type_of(a) == t_pair ? cons(car(a), do_xq(cdr(a), d, env)) : do_qq(d, env);
}

val spec_qquote(val v, val env) {
  arity(1, v, "error: syntax: qq\n");
  return do_qq(car(v), env);
}
struct { val k; val (*fn)(val, val); } forms[] = {
  { NULL, spec_if },
  { NULL, spec_def },
  { NULL, spec_set },
  { NULL, spec_lambda },
  { NULL, spec_form },
  { NULL, spec_quote },
  { NULL, spec_qquote }
};

val (*special_preinit(val k))(val, val) {
  val vs[] = { sym_if, sym_def, sym_set, sym_fn, sym_rw, sym_qt, sym_qq };
  for (int i = 0; i < sizeof(vs) / sizeof(*vs); ++i) forms[i].k = vs[i];
  return (special = special_postinit)(k);
}

val (*special_postinit(val k))(val, val) {
  for (int i = 0; i < (sizeof(forms) / sizeof(*forms)); ++i)
    if (forms[i].k == k) return forms[i].fn;
  return nil;
}

#define BINARY(as) arity(2, as, "error: wrong number of arguments\n"); val a = car(as), b = cadr(as)
#define binop(n, tp, r) val n(val as) { BINARY(as); require(a, tp); require(b, tp); return r; }
#define binop_n(n, op) binop(n, t_num, num(a->data.num op b->data.num))
binop_n(_add, +) binop_n(_sub, -) binop_n(_mul, *) binop_n(_div, /)
binop(_lt, t_num, a->data.num < b->data.num ? t : nil)
binop(_gt, t_num, a->data.num > b->data.num ? t : nil)
val _and(val as) { BINARY(as); return a && b ? b : nil; }
val _or(val as) { BINARY(as); return a ? a : b; }
val scurry(val n) { require(n, t_nil); exit(0); }
val set_hd(val as) { BINARY(as); require(a, t_pair); return car(a) = b; }
val set_tl(val as) { BINARY(as); require(a, t_pair); return cdr(a) = b; }
val assq(val), eq(val), eqish(val);
#define unop(n, t, fn) val n(val as) { require(cdr(as), t_nil); require(car(as), t); return fn(car(as)); }
unop(_car, t_pair, car) unop(_cdr, t_pair, cdr)
val _eval(val v) { require(cdr(v), t_nil); return eval_toplevel(car(v)); }
val _apply(val v) { BINARY(v); return eval_toplevel(cons(a, b)); }

void gus_initialize() {
  gc_atomic_begin();
  root.data.pair.snd = cons(nil, cons(nil, nil));

  struct { val *s; char *n; } syms[] = {
    { &t, "t" },
    { &sym_if, "if" },
    { &sym_def, "def" },
    { &sym_set, "set" },
    { &sym_fn, "fn" },
    { &sym_rw, "rw" },
    { &sym_qt, "qt" },
    { &sym_qq, "qq" },
    { &sym_uq, "uq" },
    { &sym_xq, "xq" }
  };

  for (int i = 0; i < sizeof(syms)/sizeof(*syms); i++)
    *syms[i].s = symbol(syms[i].n);

  struct { char *s; val (*p)(val); } prims[] = {
    { "assq", assq },
    { "+", _add },
    { "-", _sub },
    { "*", _mul },
    { "/", _div },
    { "zzz", scurry },
    { "<", _lt },
    { ">", _gt },
    { "and", _and },
    { "or", _or },
    { "hd<-", set_hd },
    { "tl<-", set_tl },
    { "=", eqish },
    { "eq?", eq },
    { "eval", _eval },
    { "apply", _apply }
  };

  for (int i = 0; i < sizeof(prims)/sizeof(*prims); i++)
    GLOBAL = cons(cons(symbol(prims[i].s), prim(prims[i].p, prims[i].s)), GLOBAL);

  gc_atomic_end();
  char *gl = (char*)GUS_LIB;
  while (*gl) eval_toplevel(read(&gl));
}

val eq(val args) {
  arity(2, args, "error: wrong number of arguments: eq\n");
  return car(args) == cadr(args) ? t : nil;
}
val assq(val args) {
  arity(2, args, "error: wrong number of arguments: assq\n");
  return assq_c(car(args), cadr(args));
}
val assq_c(val key, val alist) {
  for (; type_of(alist) == t_pair; alist = cdr(alist))
    if (caar(alist) == key) return car(alist);
  return nil;
}

#define EQ_ON(c) (a->data.c == b->data.c ? t : nil)
val eqish(val v) {
  BINARY(v);
  if (a == b) return t;
  if (type_of(a) != type_of(b)) return nil;
  switch (type_of(a)) {
    case t_str:  return strcmp(a->data.str, b->data.str) ? nil : t;
    case t_num:  return EQ_ON(num);
    case t_prim: return EQ_ON(prim.fn);
    default:     return nil;
  }
}

val read_num(char**), read_sym(char**), read_str(char**), read_cons(char**);
val read_val(char **str) {
  while (isspace(**str)) ++(*str);
  char c = **str;
  if (!c) return nil;
  if (c == '\'' || c == '(' || c == '"' || c == '`' || c == ',' || c == '@') {
    ++(*str);
    return c == '\'' ? cons(sym_qt, cons(read_val(str), nil)) :
           c == '`' ? cons(sym_qq, cons(read_val(str), nil)) :
           c == ',' ? cons(sym_uq, cons(read_val(str), nil)) :
           c == '@' ? cons(sym_xq, cons(read_val(str), nil)) :
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
  val v;
  if (!c) return nil;
  if (c == ')') { ++(*str); return nil; }
  if (c == '.') {
    ++(*str);
    v = read_val(str);
    while (*((*str)++) != ')');
    return v;
  }
  v = read_val(str);
  return cons(v, read_cons(str));
}

val read(char **str) {
  gc_atomic_begin();
  val v = read_val(str);
  gc_atomic_end();
  return v;
}

char quotechar(val v) {
  return v == sym_qt ? '\'' :
         v == sym_qq ? '`' :
         v == sym_uq ? ',' :
         v == sym_xq ? '@' :
         '\0';
}

void println(val d, FILE *f) { print(d, f); putc('\n', f); }
void print(val d, FILE *f) {
  char q;
  switch (type_of(d)) {
    case t_nil:  fprintf(f, "()"); break;
    case t_num:  fprintf(f, "%ld", d->data.num); break;
    case t_prim:
      fprintf(f, "#<prim %s>", d->data.prim.name);
      break;
    case t_fn:
    case t_rw:
      fprintf(f, "#");
      print(cons(d->type == t_fn ? sym_fn : sym_rw, car(d)), f);
      break;
    case t_sym:  fputs(d->data.str, f); break;
    case t_str:
      putc('"', f);
      for (char *c = d->data.str; *c; c++)
        *c == '"' ? fprintf(f, "\\\"") : putc(*c, f);
      putc('"', f);
      break;
    case t_pair:
      if ((q = quotechar(car(d))) && type_of(cdr(d)) == t_pair) {
        putc(q, f);
        print(cadr(d), f);
      } else {
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
}

jmp_buf *rescue = NULL;
void repl() {
  jmp_buf jb, *old = rescue;
  rescue = &jb;
  char buf[1024], *b = buf;
  printf("> ");
  while ((b = fgets(buf, 1024, stdin))) {
    if (setjmp(jb)) STACK = nil;
    else println(eval_toplevel(read(&b)), stdout);
    printf("> ");
  }
  rescue = old;
  puts("(zzz)");
}

void panic(int status) {
  if (rescue) {
    if (gc_atomic) gc_atomic_end();
    longjmp(*rescue, 1);
  } else exit(status);
}

int main() {
  gus_initialize();
  repl();
  return 0;
}
