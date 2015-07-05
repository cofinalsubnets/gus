#include <stdarg.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>

typedef enum {
  t_pair = 0,
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
    };
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

#define car(c) ((c)->data.fst)
#define cdr(c) ((c)->data.snd)
#define caar(c) car(car(c))
#define cadr(c) car(cdr(c))
#define cdar(c) cdr(car(c))
#define cddr(c) cdr(cdr(c))
#define type_of(x) (x ? x->type : t_nil)
#define GC_ALLOC_CYCLE (1<<15)
#define GC_MEM_MAX (1<<25)
#define MARKED 1
#define PROTECTED (1<<1)
#define ATOMIC (1<<2)
#define IS(f,h) (h->alive&f)
#define SET(f,h) (h->alive|=f)
#define UNSET(f,h) (h->alive&=~f)

char gc_atomic = 0;
unsigned long gc_allocs = 0, gc_mem = 0;
struct _val root = { { NULL, NULL }, NULL, t_pair, ~0 };
val vals = NULL;

void gc_mark(val v) {
  if (IS(MARKED, v)) return;
  SET(MARKED, v);
  t_t t = type_of(v);
  if (t == t_pair || t == t_func || t == t_form) {
    gc_mark(car(v));
    gc_mark(cdr(v));
  }
}

void gc() {
  gc_mark(&root);
  val prev = NULL, v;
  for (v = vals; v; v = v->next)
    if (v->alive) {
      UNSET(MARKED, v);
      prev = v;
    } else {
      if (prev) prev->next = v->next;
      else vals = v->next;
      t_t t = type_of(v);
      if (t == t_str || t == t_err || t == t_err_thrown) free(v->data.str);
      gc_mem -= sizeof(struct _val);
      free(v);
      v = prev ? prev->next : vals;
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
  v->alive = gc_atomic ? ATOMIC : 0;
  v->next = vals;
  v->type = t;
  vals = v;
  memset(&(v->data), 0, sizeof(union _data));
  return v;
oom:
  fprintf(stderr, "oom!\n");
  abort();
}

void gc_protect(val v) { SET(PROTECTED, v); }
void gc_unprotect(val v) { UNSET(PROTECTED, v); }
void gc_atomic_begin() { gc_atomic = 1; }
void gc_atomic_end() {
  val v = vals;
  for (; v && IS(ATOMIC, v); v = v->next) UNSET(ATOMIC, v);
}

struct st_entry {
  char *str;
  struct st_entry *next;
};

struct st_entry *symbol_table = NULL;

char *intern(char *s) {
  struct st_entry *t = symbol_table;
  for (; t; t = t->next) if (!strcmp(s, t->str)) return t->str;
  t = (struct st_entry*) malloc(sizeof(struct st_entry));
  t->next = symbol_table;
  t->str = strdup(s);
  symbol_table = t;
  return t->str;
}

#define unary(t, s, v) { val r = new(t); r->data.s = v; return r; }
#define binary(t, a, b) { val r = new(t); r->data.fst = a; r->data.snd = b; return r; }

val cons(val car, val cdr)   binary(t_pair,car, cdr)
val lambda(val def, val env) binary(t_func, def, env)
val form(val def, val env)   binary(t_form, def, env)
val string(char *s)          unary(t_str, str, strdup(s))
val symbol(char *s)          unary(t_sym, str, intern(s))
val num(long l)              unary(t_num, num, l)
val prim(val (*p)(val))      unary(t_prim, prim, p)
val error(char *s)           unary(t_err_thrown, str, strdup(s))

val sym_t, sym_eval, sym_apply, sym_if, sym_def, sym_set, sym_set_car,
    sym_set_cdr, sym_lambda, sym_form, sym_quote, workspace;

#define STACK car(workspace)
#define RET_VAL cadr(workspace)
#define GLOBAL cddr(workspace)
#define RETURN(x) { RET_VAL=x; pop_frame(); return; }
#define CONTINUE(t, d, e) { caar(STACK) = sym_##t; car(cdar(STACK)) = NULL; cadr(cdar(STACK)) = d; cddr(cdar(STACK)) = e; return; }
#define require(v, t) if (type_of(v) != t) return error("Type error: not " #t)

val (*special_preinit(val))(val, val), (*special_postinit(val))(val, val),
    (*(*special)(val))(val, val) = special_preinit,
    eval(val, val), eval_args(val, val, val*), zip(val, val), assq_c(val, val);


#define pop_frame() STACK = cdr(STACK)
void push_frame(val frame_type, val a,  val b) {
  STACK = cons(NULL, STACK);
  car(STACK) = cons(a, b);
  car(STACK) = cons(NULL, car(STACK));
  car(STACK) = cons(frame_type, car(STACK));
}

void do_eval_frame(), do_apply_frame();
void do_frame() {
  if (type_of(RET_VAL) == t_err_thrown) pop_frame();
  else {
    val frame_t = caar(STACK);
    if (frame_t == sym_eval) do_eval_frame();
    else if (frame_t == sym_apply) do_apply_frame();
    else pop_frame();
  }
}

void do_eval_frame() {
  val ev = cdar(STACK), d = cadr(ev), env = cddr(ev);
  val args, acc, fn, (*spec)(val, val);
  if (!env) RETURN(d);
  switch (type_of(d)) {
    case t_pair:
      args = cdr(d);
      if (spec = special(car(d))) RETURN(spec(args, env));
      car(ev) = acc = cons(NULL, NULL);
      fn = car(acc) = eval(car(d), env);
      t_t t = type_of(fn);
      if (t != t_prim && t != t_func && t != t_form) RETURN(NULL);
      if (t == t_prim || t == t_func) args = eval_args(args, env, &cdr(acc));
      if (t == t_prim) RETURN(fn->data.prim(args));
      CONTINUE(apply, fn, args);
    case t_sym:
      for (; env; env = cdr(env))
        if (acc = assq_c(d, car(env))) RETURN(cdr(acc));
      RETURN(NULL);
    default:
      RETURN(d);
  }
}

void do_apply_frame() {
  val ev = cdar(STACK), fn = cadr(ev), args = cddr(ev);
  gc_atomic_begin(); /* FIXME: this shouldn't rely on gc_atomic */
  val res;
  val body = cdar(fn); // HERE
  val env = cons(zip(caar(fn), args), cdr(fn));
  gc_atomic_end();
  for (; cdr(body); body = cdr(body)) eval(car(body), env);
  CONTINUE(eval, car(body), env);
}

#define eval_toplevel(v) eval(v, GLOBAL)
val eval(val d, val env) {
  val caller = STACK;
  push_frame(sym_eval, d, env);
  while (STACK != caller) do_frame();
  if (type_of(RET_VAL) == t_err_thrown) RET_VAL->type = t_err;
  return RET_VAL;
}

val zip(val a, val b) {
  if (!a || !b || a->type != t_pair || b->type != t_pair) return NULL;
  return cons(cons(car(a), car(b)), zip(cdr(a), cdr(b)));
}

val eval_args(val l, val env, val *acc) {
  if (!l || l->type != t_pair) return l;
  val tl = eval_args(cdr(l), env, acc); /* safe from gc b/c stored in acc */
  val hd = eval(car(l), env); /* safe from gc b/c stored in RET_VAL */
  return *acc = cons(hd, tl);
}

val spec_if(val, val), spec_def(val, val), spec_set(val, val),
    spec_set_car(val, val), spec_set_cdr(val, val),
    spec_lambda(val, val), spec_form(val, val), spec_quote(val, val);

struct {
  val name;
  val (*fn)(val, val);
} forms[] = {
  { NULL, spec_if },
  { NULL, spec_def },
  { NULL, spec_set },
  { NULL, spec_set_car },
  { NULL, spec_set_cdr },
  { NULL, spec_lambda },
  { NULL, spec_form },
  { NULL, spec_quote }
};

val (*special_preinit(val k))(val, val) {
  forms[0].name = sym_if;
  forms[1].name = sym_def;
  forms[2].name = sym_set;
  forms[3].name = sym_set_car;
  forms[4].name = sym_set_cdr;
  forms[5].name = sym_lambda;
  forms[6].name = sym_form;
  forms[7].name = sym_quote;
  special = special_postinit;
  special_postinit(k);
}

val (*special_postinit(val k))(val, val) {
  int i;
  if (!k || k->type != t_sym) return NULL;
  for (i = 0; i < (sizeof(forms) / sizeof(*forms)); ++i)
    if (forms[i].name->data.str == k->data.str) return forms[i].fn;
  return NULL;
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
  caar(env) = cons(k, NULL);
  cdr(caar(env)) = eval(x, env);
  return cdr(caar(env));
}

val spec_set(val b, val env) {
  require_binary(b);
  val k = car(b);
  require(k, t_sym);
  val kv = assq_c(k, env);
  if (kv) cdr(kv) = eval(cadr(b), env);
  return cdr(kv);
}

val spec_set_car(val b, val env) {
  require_binary(b);
  val p = eval(car(b), env), x = cadr(b);
  require(p, t_pair);
  car(b) = eval(x, env);
  return car(b);
}

val spec_set_cdr(val b, val env) {
  require_binary(b);
  val p = eval(car(b), env), x = cadr(b);
  require(p, t_pair);
  cdr(b) = eval(x, env);
  return cdr(b);
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

val spec_quote(val v, val env) { return car(v); }
val assq(val), eq(val);

#define sym(n,s) sym_##n = symbol(s)
#define binop(n, op) val n(val args) { require_binary(args); require(car(args), t_num); require(cadr(args), t_num); return num(car(args)->data.num op cadr(args)->data.num); }
binop(_add, +)
binop(_sub, -)
binop(_mul, *)
binop(_div, /)
#undef binop
#define unop(n, t, fn) val n(val args) { require(cdr(args), t_nil); require(car(args), t); return fn(car(args)); }
unop(_car, t_pair, car)
unop(_cdr, t_pair, cdr)
#undef unop

void add_binding(val env, val k, val v) {
  cdr(env) = cons(car(env), cdr(env));
  car(env) = cons(k, v);
}

void initialize() {
  gc_atomic_begin();

  sym(eval, "eval");
  sym(apply, "apply");
  sym(if, "if");
  sym(def, "def");
  sym(set, "set");
  sym(t, "t");
  sym(set_car, "set-car");
  sym(set_cdr, "set-cdr");
  sym(lambda, "lambda");
  sym(form, "form");
  sym(quote, "quote");

  val global = cons(cons(symbol("eq?"), prim(eq)), NULL);
  root.data.fst = workspace = cons(NULL, cons(NULL, cons(global, NULL)));

  add_binding(global, symbol("assq"), prim(assq));
  add_binding(global, symbol("+"),    prim(_add));
  add_binding(global, symbol("-"),    prim(_sub));
  add_binding(global, symbol("*"),    prim(_mul));
  add_binding(global, symbol("/"),    prim(_div));
  add_binding(global, symbol("car"),  prim(_car));
  add_binding(global, symbol("cdr"),  prim(_cdr));

  gc_atomic_end();
}


#define EQON(c) (a->data.c == b->data.c ? sym_t : NULL)
val eq_c(val a, val b) {
  if (a == b) return sym_t;
  if (type_of(a) != type_of(b)) return NULL;
  switch (a->type) {
    case t_str:  return strcmp(a->data.str, b->data.str) ? NULL : sym_t;
    case t_num:  return EQON(num);
    case t_sym:  return EQON(str);
    case t_prim: return EQON(prim);
    default:     return NULL;
  }
}

val eq(val args) {
  require_binary(args);
  return eq_c(car(args), cadr(args));
}

val assq_c(val key, val alist) {
  while (type_of(alist) == t_pair) {
    if (eq_c(caar(alist), key)) return car(alist);
    alist = cdr(alist);
  }
  return NULL;
}

val assq(val args) {
  require_binary(args);
  return assq_c(car(args), cadr(args));
}

char read_num(char**, val);
val read_sym(char**);
val read_str(char**);
val read_cons(char**);

val read(char **str) {
  while (**str && isspace(**str)) (*str)++;
  char c = **str;
  if (c == '\'' || c == '(' || c == '"') {
    ++(*str);
    return c == '\'' ? cons(sym_quote, cons(read(str), NULL)) :
           c == '(' ? read_cons(str) :
           read_str(str);
  }
  val d = num(0);
  return read_num(str, d) ? d : read_sym(str);
}

char read_num(char **str, val d) {
  char *end = NULL;
  long n = strtol(*str, &end, 10);
  if (*str == end) return 0;
  d->data.num = n;
  *str = end;
  return 1;
}

val read_sym(char **str) {
  char buf[100];
  memset(buf, 0, 100);
  long chars = sscanf(*str, "%99[^( \n\t\v\r\f)\"']", buf);
  *str += strlen(buf);
  return symbol(strdup(buf));
}

val read_str(char **str) {
  return NULL;
}

val read_cons(char **str) {
  char c = **str;
  if (c == ')' || c == '.') {
    ++(*str);
    return (c == '.') ? read(str) : NULL;
  }
  val v = read(str);
  return cons(v, read_cons(str));
}

void print(val d, FILE *f) {
  switch (type_of(d)) {
    case t_nil:  fprintf(f, "()"); break;
    case t_num:  fprintf(f, "%d", d->data.num); break;
    case t_func: 
    case t_prim: fputs("<function>", f); break;
    case t_err:
    case t_err_thrown:
    case t_sym:  fputs(d->data.str, f); break;
    case t_str:
      putc('"', f);
      char *c = d->data.str;
      for (; *c; c++) *c == '"' ? fprintf(f, "\\\"") : putc(*c, f);
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

void println(val d, FILE *f) {
  print(d, f);
  putc('\n', f);
}

void repl() {
  char buf[100], *b = buf;
  printf(">> ");
  while (b = fgets(buf, 100, stdin)) {
    printf("=> ");
    println(eval_toplevel(read(&b)), stdout);
    printf(">> ");
  }
  puts("*scurry*");
}

int main() {
  initialize();
  repl();
  return 0;
}
