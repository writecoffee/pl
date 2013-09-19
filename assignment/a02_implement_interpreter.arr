#lang pyret/whalesong

C = cs173.interp-basic
parse = cs173.interp-basic.parse

fun eval(prog :: String) -> C.Value:
  interp(parse(read-sexpr(prog)))
end

fun interp(prog :: C.Expr) -> C.Value:
  interp-env(prog, C.mt-env)
end

fun do-operation(op :: C.Operator, left :: C.Value, right :: C.Value) -> C.Value:
  cases (C.Operator) op:
    | plus =>
        C.numV(left.value + right.value)
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

fun interp-env(prog :: C.Expr, env :: C.Env) -> C.Value:
  cases (C.Expr) prog:
    | num(n) => C.numV(n)
    | str(s) => C.strV(s)
    | bop(op, left, right) =>
        do-operation(op, interp-env(left, env), interp-env(right, env))
  end
where:
  eval('5') is C.numV(5)
  eval('(+ 3 3)') is C.numV(6)
  eval('(+ "hello " "world")') raise "unappliable"
  eval('(- 3 3)') is C.numV(0)
  eval('(++ "hello " "world")') is C.strV("hello world")
  eval('(== "hello" "hello")') is C.strV("true")
end
