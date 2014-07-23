#lang pyret/whalesong

C = cs173.interp-basic
parse = cs173.interp-basic.parse

fun lookup(s :: String, env :: C.Env) -> C.Value:
  cases (C.Env) env:
    | mt-env => raise("unbound identifier: " + s)
    | an-env(fn, v, e) =>
        if s == fn:
          v
        else:
          lookup(s, e)
        end
  end
end

fun eval(prog :: String) -> C.Value:
  interp(parse(read-sexpr(prog)))
end

fun interp(prog :: C.Expr) -> C.Value:
  interp-env(prog, C.mt-env)
end

fun do-operation(op :: C.Operator, left :: C.Value, right :: C.Value) -> C.Value:
  cases (C.Operator) op:
    | plus =>
      cases (C.Value) left:
        | funV(_, _, _) => raise("illegal operand")
        | strV(_) => raise("illegal operand")
        | numV(n) => n
      end
      cases (C.Value) right:
        | funV(_, _, _) => raise("illegal operand")
        | strV(_) => raise("illegal operand")
        | numV(n) => C.numV(left.value + right.value)
      end
    | minus =>
      cases (C.Value) left:
        | funV(_, _, _) => raise("illegal operand")
        | strV(_) => raise("illegal operand")
        | numV(n) => n
      end
      cases (C.Value) right:
        | funV(_, _, _) => raise("illegal operand")
        | strV(_) => raise("illegal operand")
        | numV(n) => C.numV(left.value - right.value)
      end
    | append =>
      cases (C.Value) left:
        | funV(_, _, _) => raise("illegal operand")
        | numV(_) => raise("illegal operand")
        | strV(s) => s
      end
      cases (C.Value) right:
        | funV(_, _, _) => raise("illegal operand")
        | numV(_) => raise("illegal operand")
        | strV(n) => C.strV(left.value + right.value)
      end
    | str-eq =>
      cases (C.Value) left:
        | funV(_, _, _) => raise("illegal operand")
        | numV(_) => raise("illegal operand")
        | strV(s) => s
      end
      cases (C.Value) right:
        | funV(_, _, _) => raise("illegal operand")
        | numV(_) => raise("illegal operand")
        | strV(n) =>
          if left.value.contains(right.value) and right.value.contains(left.value):
            C.numV(1)
          else:
            C.numV(0)
          end
      end
  end
end

fun interp-args(args :: List<String>, params :: List<String>, env :: C.Env) -> C.Env:
  cases (List<String>) args:
    | empty =>
      cases (List<String>) params:
        | link(_, _) => raise("arity mismatch")
        | empty => C.mt-env
      end
    | link(ae, a-nxt) =>
      cases (List<String>) params:
        | empty => raise("arity mismatch")
        | link(an, p-nxt) =>
          C.an-env(an, interp-env(ae, env), interp-args(a-nxt, p-nxt, env))
      end
  end
end

# fun local-subst-list(with :: C.Expr, at :: String, lin :: 

fun local-subst(with :: C.Expr, at :: String, in :: C.Expr) -> C.Expr:
  cases (C.Expr) in:
    | num(n) =>
      in
    | str(s) =>
      in
    | id(s) =>
      if s == at:
        with
      else:
        in
      end
    | bop(op, left, right) =>
      C.bop(op, local-subst(with, at, left), local-subst(with, at, right))
    | app(f, al) =>
      C.app(f, local-subst(with, at, al))
    | cif(c, sq, alt) =>
      C.cif(local-subst(with, at, c), local-subst(with, at, sq), local-subst(with, at, alt))
  end
end

fun interp-env(prog :: C.Expr, env :: C.Env) -> C.Value:
  cases (C.Expr) prog:
    | num(n) =>
      C.numV(n)
    | str(s) =>
      C.strV(s)
    | lam(plst, bd) =>
      C.funV(plst, bd, env)
    | bop(op, left, right) =>
      do-operation(op, interp-env(left, env), interp-env(right, env))
    | id(s) =>
      lookup(s, env)
    | app(f, al) =>
      interp-env(f.body, interp-args(al, f.params, env))
    | cif(c, sq, alt) =>
      if interp-env(c, env).value <> 0:
        interp-env(sq, env)
      else:
        interp-env(alt, env)
      end
    | let(n, e, body) =>
      interp-env(local-subst(e, n, body), env)
  end
where:
  eval('5') is C.numV(5)
  eval('"My name is parat"') is C.strV("My name is parat")
  eval('(fun (x y) (+ x y))') is C.funV(["x", "y"], C.bop(C.plus, C.id("x"), C.id("y")), C.mt-env)

  eval('(+ 3 3)') is C.numV(6)
  eval('(+ "hello " "world")') raises "illegal operand"
  eval('(+ 3 "world")') raises "illegal operand"
  eval('(+ "Hello" 9)') raises "illegal operand"
  eval('(+ 3 (fun (x y) (+ x y)))') raises "illegal operand"
  eval('(+ (fun (x y) (+ x y)) 3)') raises "illegal operand"
  eval('(- 3 3)') is C.numV(0)
  eval('(- "hello " "world")') raises "illegal operand"
  eval('(- 3 "world")') raises "illegal operand"
  eval('(- "Hello" 9)') raises "illegal operand"
  eval('(- 3 (fun (x y) (+ x y)))') raises "illegal operand"
  eval('(- (fun (x y) (+ x y)) 3)') raises "illegal operand"

  eval('(++ "hello " "world")') is C.strV("hello world")
  eval('(++ "hello " 8)') raises "illegal operand"
  eval('(++ 8 "hello")') raises "illegal operand"
  eval('(++ 6 9)') raises "illegal operand"
  eval('(++ "hello" (fun (x y) (+ x y)))') raises "illegal operand"
  eval('(++ (fun (x y) (+ x y)) "hello")') raises "illegal operand"
  eval('(== "hello" "hello")') is C.numV(1)
  eval('(== "hello" "bybye")') is C.numV(0)
  eval('(== "hello" 1)') raises "illegal operand"
  eval('(== 1 "hello")') raises "illegal operand"
  eval('(== "hello" (fun (x y) (+ x y)))') raises "illegal operand"
  eval('(== (fun (x y) (+ x y)) "hello")') raises "illegal operand"

  eval('((fun () (+ 1 2)))')
    is C.numV(3)
  eval('((fun (x) (+ x 1)) 3)')
    is C.numV(4)
  eval('((fun (x y) (+ x y)) 3 7)')
    is C.numV(10)
  eval('((fun (x y) (+ x y)) )')
    raises "arity mismatch"
  eval('((fun (x y) (+ x y)) 3)')
    raises "arity mismatch"
  eval('((fun (x y) (+ x y)) 3 7 9)')
    raises "arity mismatch"
  eval('((fun (x y) (+ x y)) 3 m)')
    raises "unbound identifier: m"
  eval('((fun (x y) x) 3 7)')
    is C.numV(3)
  eval('((fun (x y) (fun (m n) (* m n))) 3 7)')
    is C.funV(["m", "n"], C.app(C.id("*"), [C.id("m"), C.id("n")]), C.an-env("x", C.numV(3), C.an-env("y", C.numV(7), C.mt-env)))
  eval('((fun (x y) (fun (x y) (* x y))) 3 7)')
    is C.funV(["x", "y"], C.app(C.id("*"), [C.id("x"), C.id("y")]), C.an-env("x", C.numV(3), C.an-env("y", C.numV(7), C.mt-env)))
  eval('((fun (x y) ((fun (x y) (+ x y)) 1 1)) 3 7)')
    is C.numV(2)

  eval('(if 1 "yes" "no")') is C.strV("yes") 
  eval('(if 0 "yes" "no")') is C.strV("no") 
  eval('(if "str cond" "yes" "no")') is C.strV("yes") 

  eval('(let (x 3) (+ x 3))') is C.numV(6)
  eval('(let (tempting-lp (fun () (3))) (tempting-lp ())') is C.numV(3)
  
end
