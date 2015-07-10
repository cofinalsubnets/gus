#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <setjmp.h>
#include <stdarg.h>

typedef enum {
  t_pair = 1,
  t_fn   = 1<<1,
  t_rw   = 1<<2,
  t_prim = 1<<3,
  t_num  = 1<<4,
  t_sym  = 1<<5,
  t_str  = 1<<6,
  t_nil  = 1<<7
} t_t;

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
#define FOREACH(i, x) for (int i = 0; i < sizeof(x)/sizeof(*x); ++i)
#define PANIC(s, ...) { fprintf(stderr, "error: " s, ##__VA_ARGS__); panic(1); }

char gc_enabled = 1;
unsigned long gc_allocs = 0, gc_mem = 0;
struct _val root = { { { nil, nil } }, NULL, t_pair, 0 };
val vals = &root;

void gc_mark(val v) {
  if (!v || v->alive) return;
  v->alive = 1;
  if (type_of(v) & (t_pair | t_fn | t_rw)) gc_mark(car(v)), gc_mark(cdr(v));
}

void gc() {
  if (!gc_enabled) return;
  gc_mark(&root);
  for (val prev = NULL, v = vals; v;)
    if (v->alive) {
      v->alive = 0, prev = v, v = v->next;
    } else {
      prev ? (prev->next = v->next) : (vals = v->next);
      if (v->type & (t_str | t_sym)) free(v->data.str);
      gc_mem -= sizeof(struct _val);
      free(v);
      v = (prev ? prev->next : vals);
    }
}

val new(t_t t) {
  if (gc_mem + sizeof(struct _val) > GC_MEM_MAX) {
    gc();
    if (gc_mem + sizeof(struct _val) > GC_MEM_MAX) goto oom;
  }

  if ((++gc_allocs) % GC_ALLOC_CYCLE == 0) gc();
  val v = (val) malloc(sizeof(struct _val));
  if (!v) goto oom;
  gc_mem += sizeof(struct _val);
  v->alive = 0, v->next = vals, v->type = t;
  memset(&(v->data), 0, sizeof(union _data));
  return vals = v;
oom:
  fprintf(stderr, "error: out of memory after %lu allocations.\n", gc_allocs);
  exit(1);
}

const int t_any = t_pair | t_fn | t_rw | t_prim | t_num | t_sym | t_str | t_nil;
void tc(val v, const char *name, int var, int req, ...) {
  va_list ap; int n;
  va_start(ap, req);
  for (n = 0; type_of(v) == t_pair && n < req; ++n, v = cdr(v))
    if (!(type_of(car(v)) & va_arg(ap, int)))
      PANIC("%s: wrong type for argument %d\n", name, n+1);
  if (v && !var) PANIC("%s: too many arguments (%d needed)\n", name, req);
  if (n < req) PANIC("%s: not enough arguments: %d for %d\n", name, n, req);
}

#define STACK root.data.pair.fst
#define RET_VAL car(root.data.pair.snd)
#define GLOBAL cadr(root.data.pair.snd)
#define SYMBOL_TABLE cddr(root.data.pair.snd)
val t, sym_if, sym_def, sym_set, sym_fn, sym_rw, sym_qt, sym_qq, sym_uq,
    sym_xq, sym_repl, (*special(val))(val, val), eval_args(val, val, val*),
    assq_c(val, val), zip(val, val);

val cons(val a, val b) { val r = new(t_pair); return car(r) = a, cdr(r) = b, r; }
val lambda(val a, val b) { val r = new(t_fn); return car(r) = a, cdr(r) = b, r; }
val form(val a, val b) { val r = new(t_rw); return car(r) = a, cdr(r) = b, r; }
val string(char *s) { val r = new(t_str); return r->data.str = strdup(s), r; }
val num(long l) { val r = new(t_num); return r->data.num = l, r; }

val prim(val (*const f)(val), char *n) {
  val p = new(t_prim);
  return p->data.prim.fn = f, p->data.prim.name = n, p;
}

val symbol(char *s) {
  for (val st = SYMBOL_TABLE; st; st = cdr(st))
    if (!strcmp(car(st)->data.str, s)) return car(st);
  SYMBOL_TABLE = cons(nil, SYMBOL_TABLE);
  val v = new(t_sym);
  return v->data.str = strdup(s), car(SYMBOL_TABLE) = v;
}

#define STACK_LIMIT 10000
unsigned long stack_height = 0;
void _return(val x) {
  RET_VAL = x, STACK = cdr(STACK), --stack_height;
}

void _continue(val s, val a, val b) {
  caar(STACK)       = s;
  car(cdar(STACK))  = nil;
  cadr(cdar(STACK)) = a;
  cddr(cdar(STACK)) = b;
}

void do_eval(), do_apply();
#define eval(d, env) _call(t, d, env)
val _call(val tag, val a, val b) {
  if (++stack_height > STACK_LIMIT) PANIC("stack overflow\n");
  val caller = STACK;
  gc_enabled = 0;
  STACK = cons(cons(tag, cons(nil, cons(a, b))), STACK);
  gc_enabled = 1;
  while (STACK != caller) caar(STACK) ? do_eval() : do_apply();
  return RET_VAL;
}

void do_eval() {
  val ev = cdar(STACK), d = cadr(ev), env = cddr(ev), acc, fn, (*sp)(val, val);
  switch (type_of(d)) {
    case t_pair:
      if ((sp = special(car(d)))) return _return(sp(cdr(d), env));
      car(ev) = acc = cons(nil, nil), fn = car(acc) = eval(car(d), env);
      if (type_of(fn) == t_rw)
        return _continue(t, _call(nil, fn, cdr(d)), env);
      if (type_of(fn) & (t_prim | t_fn))
        return _continue(nil, fn, eval_args(cdr(d), env, &cdr(acc)));
      fprintf(stderr, "error: not applicable: "), println(fn, stderr), panic(1);
    case t_sym:
      for (; env; env = cdr(env))
        if ((acc = assq_c(d, car(env)))) return _return(cdr(acc));
      fprintf(stderr, "error: not defined: "), println(d, stderr), panic(1);
    default:
      _return(d);
  }
}

void do_apply() {
  val ev = cdar(STACK), fn = cadr(ev), args = cddr(ev);
  if (type_of(fn) == t_prim) return _return(fn->data.prim.fn(args));
  gc_enabled = 0;
  val body = cdar(fn), env = car(ev) = cons(zip(caar(fn), args), cdr(fn));
  gc_enabled = 1;
  for (; type_of(cdr(body)) == t_pair; body = cdr(body)) eval(car(body), env);
  _continue(t, car(body), env);
}

val eval_args(val l, val env, val *acc) {
  if (type_of(l) != t_pair) return l;
  val tl = eval_args(cdr(l), env, acc); /* safe from gc b/c stored in acc */
  return *acc = cons(eval(car(l), env), tl); /* hd is in RET_VAL when consed */
}

val zip(val a, val b) {
  t_t ta = type_of(a), tb = type_of(b);
  if (ta == t_nil && tb == ta) return nil;
  if (ta == t_nil) PANIC("too many arguments\n");
  if (ta == t_pair && tb != ta) PANIC("not enought arguments\n");
  if (ta != t_pair) return cons(cons(a, b), nil);
  return cons(cons(car(a), car(b)), zip(cdr(a), cdr(b)));
}

val spec_if(val b, val env) {
  return tc(b, "if", 0, 3, t_any, t_any, t_any),
         eval(eval(car(b), env) ? cadr(b) : car(cddr(b)), env);
}

val spec_set(val b, val env) {
  tc(b, "set", 0, 2, t_sym, t_any);
  for (val kv, k = car(b); env; env = cdr(env))
    if ((kv = assq_c(k, car(env)))) return cdr(kv) = eval(cadr(b), env);
  return nil;
}

val spec_fn(val b, val env) {
  return tc(b, "fn", 1, 2, t_pair | t_sym | t_nil, t_any), lambda(b, env);
}

val spec_rw(val b, val env) {
  return tc(b, "rw", 1, 2, t_pair | t_sym | t_nil, t_any), form(b, env);
}

val spec_qt(val v, val env) {
  return tc(v, "qt", 0, 1, t_any), car(v);
}

val spec_def(val b, val env) {
  tc(b, "def", 0, 2, t_sym, t_any);
  car(cdar(STACK)) = cons(car(b), eval(cadr(b), env));
  cdar(env) = cons(caar(env), cdar(env));
  caar(env) = car(cdar(STACK));
  return cdar(cdar(STACK));
}

val xq(val, val, val);
val qq(val v, val env) {
  if (type_of(v) != t_pair || car(v) == sym_qq) return v;
  else if (car(v) == sym_uq) return eval(cadr(v), env);
  else if (type_of(car(v)) == t_pair && caar(v) == sym_xq)
    return xq(eval(car(cdar(v)), env), cdr(v), env);
  else return cons(qq(car(v), env), qq(cdr(v), env));
}

val xq(val a, val d, val env) {
  return type_of(a) == t_pair ? cons(car(a), xq(cdr(a), d, env)) : qq(d, env);
}

val spec_qq(val v, val env) {
  return tc(v, "qq", 0, 1, t_any), qq(car(v), env); /* FIXME: gc-unsafe! */
}

void repl(val);
val spec_repl(val v, val env) { repl(env); return RET_VAL; }

val (*special(val k))(val, val) {
  static const struct { val *const k; val (*const fn)(val, val); } sfs[] = {
    { &sym_if, spec_if },   { &sym_def, spec_def },
    { &sym_set, spec_set }, { &sym_fn, spec_fn },
    { &sym_rw, spec_rw },   { &sym_qt, spec_qt },
    { &sym_qq, spec_qq },   { &sym_repl, spec_repl }
  };
  FOREACH(i, sfs) if (*sfs[i].k == k) return sfs[i].fn;
  return nil;
}

#define unop(n, t, fn) val n(val as) { return tc(as, #n, 0, 1, t), fn(car(as)); }
unop(hd, t_pair, car) unop(tl, t_pair, cdr)
#define typep(n, nn, ts) val tp_##n(val as) { return tc(as, nn, 0, 1, t_any), type_of(car(as)) & (ts) ? t : nil; }
typep(pair, "pair?", t_pair) typep(num, "num?", t_num) typep(str, "str?", t_str)
typep(sym, "sym?", t_sym) typep(fn, "fn?", t_fn | t_prim) typep(rw, "rw?", t_rw)
#define binop(n, name, ta, tb, r) val n(val as) { return tc(as, name, 0, 2, ta, tb), r; }
#define binop_n(n, op) binop(n, #op, t_num, t_num, num(car(as)->data.num op cadr(as)->data.num))
binop_n(_add, +) binop_n(_sub, -) binop_n(_mul, *)
val _div(val as) {
  tc(as, "/", 0, 2, t_num, t_num);
  long a = car(as)->data.num, b = cadr(as)->data.num;
  if (b == 0) PANIC("divide by zero\n");
  return num(a / b);
}

binop(_lt, "<", t_num, t_num, car(as)->data.num < cadr(as)->data.num ? t : nil)
binop(_gt, ">", t_num, t_num, car(as)->data.num > cadr(as)->data.num ? t : nil)
binop(set_hd, "set-hd", t_pair, t_any, caar(as) = cadr(as))
binop(set_tl, "set-tl", t_pair, t_any, cdar(as) = cadr(as))
binop(_apply, "apply", t_fn | t_prim, t_pair, _call(nil, car(as), cadr(as)))
val scurry(val n) { tc(n, "zzz", 0, 0); exit(0); }
val _eval(val v) { return tc(v, "eval", 0, 1, t_any), eval(car(v), GLOBAL); }

val eq(val args) {
  return tc(args, "eq", 0, 2, t_any, t_any), car(args) == cadr(args) ? t : nil;
}

val assq(val args) {
  return tc(args, "assq", 0, 2, t_any, t_pair), assq_c(car(args), cadr(args));
}

val assq_c(val k, val kvs) {
  for (; type_of(kvs) == t_pair; kvs = cdr(kvs))
    if (caar(kvs) == k) return car(kvs);
  return nil;
}

val eqish(val v) {
  tc(v, "=", 0, 2, t_any, t_any);
  val a = car(v), b = cadr(v);
  if (a == b) return t;
  if (type_of(a) != type_of(b)) return nil;
  switch (type_of(a)) {
    case t_str:  return strcmp(a->data.str, b->data.str) ? nil : t;
    case t_num:  return a->data.num == b->data.num ? t : nil;
    default:     return nil;
  }
}

void initialize() {
  static const struct { val *const s; char *n; } syms[] = {
    { &t, "t" },         { &sym_if, "if" },     { &sym_def, "def" },
    { &sym_set, "set" }, { &sym_fn, "fn" },     { &sym_rw, "rw" },
    { &sym_qt, "qt" },   { &sym_qq, "qq" },     { &sym_uq, "uq" },
    { &sym_xq, "xq" },   { &sym_repl, "repl" }
  };
  static const struct { char *s; val (*const p)(val); } prims[] = {
    { "assq", assq },     { "+", _add },         { "-", _sub },
    { "*", _mul },        { "/", _div },         { "zzz", scurry },
    { "<", _lt },         { ">", _gt },          { "set-hd", set_hd },
    { "set-tl", set_tl }, { "=", eqish },        { "eq?", eq },
    { "eval", _eval },    { "apply", _apply },   { "hd", hd },
    { "tl", tl },         { "pair?", tp_pair },  { "num?", tp_num },
    { "str?", tp_str },   { "sym?", tp_sym },    { "fn?", tp_fn },
    { "rw?", tp_rw }
  };
  gc_enabled = 0;
  root.data.pair.snd = cons(nil, cons(cons(nil, nil), nil));
  FOREACH(i, syms) *syms[i].s = symbol(syms[i].n);
  FOREACH(i, prims) car(GLOBAL) =
    cons(cons(symbol(prims[i].s), prim(prims[i].p, prims[i].s)), car(GLOBAL));
  gc_enabled = 1;
}

const struct { const char c; val *const s; } qchars[] = {
  { '\'', &sym_qt }, { '`', &sym_qq }, { ',', &sym_uq },  { '@', &sym_xq }
};

char quotechar(val v) {
  FOREACH(i, qchars) if (*qchars[i].s == v) return qchars[i].c;
  return 0;
}

val charquote(char c) {
  FOREACH(i, qchars) if (qchars[i].c == c) return *qchars[i].s;
  return nil;
}

val read_num(char**), read_sym(char**), read_str(char**), read_cons(char**);
val read_val(char **str) {
  while (isspace(**str)) ++(*str);
  char c = **str;
  if (!c) return nil;
  val v = charquote(c);
  if (v) return ++(*str), cons(v, cons(read_val(str), nil));
  if (c == '(') return ++(*str), read_cons(str);
  if (c == '"') return ++(*str), read_str(str);
  return (v = read_num(str)) ? v : read_sym(str);
}

val read_num(char **str) {
  char *end = NULL;
  long n = strtol(*str, &end, 10);
  if (*str == end) return NULL; 
  return *str = end, num(n);
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
  for (; **str && **str != '"'; ++(*str)) if (**str == '\\') ++(*str);
  val s = string(strndup(start, *str - start));
  if (**str) ++(*str);
  return s;
}

val read_cons(char **str) {
  while (isspace(**str)) ++(*str);
  char c = **str;
  if (!c) return nil;
  if (c == ')') return ++(*str), nil;
  if (c == '.') {
    ++(*str);
    val v = read_val(str);
    while (*((*str)++) != ')');
    return v;
  }
  return cons(read_val(str), read_cons(str));
}

val read(char **str) {
  gc_enabled = 0;
  val v = read_val(str);
  gc_enabled = 1;
  return v;
}

void println(val d, FILE *f) { print(d, f); putc('\n', f); }
void print(val d, FILE *f) {
  char q;
  switch (type_of(d)) {
    case t_nil:  fprintf(f, "()"); break;
    case t_num:  fprintf(f, "%ld", d->data.num); break;
    case t_prim: fprintf(f, "#%s", d->data.prim.name); break;
    case t_sym:  fputs(d->data.str, f); break;
    case t_fn:
    case t_rw:
      fputc('#', f), print(cons(d->type == t_fn ? sym_fn : sym_rw, car(d)), f);
      break;
    case t_str:
      putc('"', f);
      for (char *c = d->data.str; *c; ++c)
        *c == '"' ? fprintf(f, "\\\"") : putc(*c, f);
      putc('"', f);
      break;
    case t_pair:
      if ((q = quotechar(car(d))) && type_of(cdr(d)) == t_pair) {
        putc(q, f), print(cadr(d), f);
      } else {
        putc('(', f);
        print(car(d), f);
        for (d = cdr(d); type_of(d) == t_pair; d = cdr(d))
          putc(' ', f), print(car(d), f);
        if (d) fprintf(f, " . "), print(d, f);
        putc(')', f);
      }
  }
}

jmp_buf *rescue = NULL;
void repl(val env) {
  char buf[1024], *b;
  jmp_buf jb, *old = rescue;
  rescue = &jb;
  val sp = STACK;
  RET_VAL = nil;

  printf(">> ");
  while ((b = fgets(buf, 1024, stdin))) {
    if (setjmp(jb)) STACK = sp;
    else RET_VAL = eval(read(&b), env), printf("=> "), println(RET_VAL, stdout);
    printf(">> ");
  }

  rescue = old;
  putchar('\n');
}

void panic(int status) {
  if (!rescue) exit(status);
  gc_enabled = 1;
  longjmp(*rescue, status);
}

int main() {
  initialize();
  repl(GLOBAL);
  return 0;
}
