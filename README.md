Scheme 语言子集编译器，生成 x86-64 汇编代码。

```
Program   ----> Expr
Expr      ----> constant
            |   var
            |   (quote datum)
            |   (if Expr Expr)
            |   (if Expr Expr Expr)
            |   (and Expr*)
            |   (or Expr*)
            |   (not Expr)
            |   (begin Expr* Expr)
            |   (lambda (var*) Expr+)
            |   (let ([var Expr]*) Expr+)
            |   (letrec ([var Expr]*) Expr+)
            |   (set! var Expr)
            |   (primitive Expr*)
            |   (Expr Expr*)
```

- constant is #t, #f, (), or a fixnum;
- fixnum is an exact integer;
- datum is a constant, pair of datums, or vector of datums; and
- var is an arbitrary symbol.
