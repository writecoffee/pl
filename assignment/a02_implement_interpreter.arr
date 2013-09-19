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
        | strV(s) => raise("illegal operand")
        | numV(n) => n
      end
      cases (C.Value) right:
        | strV(s) => raise("illegal operand")
        | numV(n) => C.numV(left.value + right.value)
      end
    | minus =>
      C.numV(left.value - right.value)
    | append =>
      C.strV(left.value + right.value)
    | str-eq =>
      if left.value.contains(right.value) and right.value.contains(left.value):
        C.strV("true")
      else:
        C.strV("false")
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

fun interp-env(prog :: C.Expr, env :: C.Env) -> C.Value:
  cases (C.Expr) prog:
    | num(n) =>
      C.numV(n)
    | str(s) =>
      C.strV(s)
    | bop(op, left, right) =>
      do-operation(op, interp-env(left, env), interp-env(right, env))
    | id(s) =>
      lookup(s, env)
    | app(f, al) =>
      interp-env(f.body, interp-args(al, f.params, env))
  end
where:
  eval('5') is C.numV(5)
  eval('"My name is pyrat"') is C.strV("My name is pyrat")

  eval('(+ 3 3)') is C.numV(6)
  eval('(+ "hello " "world")') raises "illegal operand"
  eval('(+ 3 "world")') raises "illegal operand"
  eval('(+ "Hello" 9)') raises "illegal operand"
  eval('(- 3 3)') is C.numV(0)

  eval('(++ "hello " "world")') is C.strV("hello world")
  eval('(== "hello" "hello")') is C.strV("true")

  eval('((fun (x) (+ x 1)) 3)') is C.numV(4)
  eval('((fun (x) (+ x 1)) "hello")') raises "illegal operand"

  eval('((fun (x y) (+ x y)) 3 7)') is C.numV(10)
  eval('((fun (x y) (+ x y)) )') raises "arity mismatch"
  eval('((fun (x y) (+ x y)) 3)') raises "arity mismatch"
  eval('((fun (x y) (+ x y)) 3 7 9)') raises "arity mismatch"

end
