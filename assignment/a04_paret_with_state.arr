#lang pyret/whalesong

data Value :
  | numV(value :: Number)
  | strV(value :: String)
  | funV(params :: List<String>, body :: Expr, env :: Env)
end
 
data Env:
  | mt-env
  | an-env(name :: String, loc :: String, env :: Env)
end
 
data Store:
  | mt-store
  | a-store(loc :: String, val :: Value, store :: Store)
end
 
data Result :
  | result(val :: Value, store :: Store)
end
 
data Expr:
  | idE(name :: String)
  | numE(value :: Number)
  | strE(value :: String)
  | bopE(op :: Operator, left :: Expr, right :: Expr)
  | cifE(cond :: Expr, consq :: Expr, altern :: Expr)
  | letE(name :: String, expr :: Expr, body :: Expr)
  | lamE(params :: List<String>, body :: Expr)
  | appE(func :: Expr, args :: List<Expr>)
 
  | assignE(name :: String, expr :: Expr)
  | doE(exprs :: List<Expr>)
end
 
data Operator:
  | plus
  | minus
  | append
  | str-eq
end
 
fun parse(prog) -> Expr:
  doc: "Parse a string matching Paret's concrete syntax into an Expr."
 
  fun check-params(params :: List<String>) -> List<String>:
    doc: "Ensure that a function has no duplicate parameter names."
    for each(param from params):
      when params.filter(fun(x): x == param end).length() > 1:
        raise("parse: function has duplicate parameter " + param)
      end
    end
    params
  end
 
  fun convert(sexpr):
    doc: "nvert an s-expression into an Expr."
    if List(sexpr):
      head = sexpr.first
      if head == "string":
        strE(sexpr.get(1))
      else if head == "if":
        cifE(convert(sexpr.get(1)),
                   convert(sexpr.get(2)),
             convert(sexpr.get(3)))
      else if head == "let":
        letE(sexpr.get(1).get(0),
             convert(sexpr.get(1).get(1)),
             convert(sexpr.get(2)))
      else if head == "assign":
        assignE(sexpr.get(1), convert(sexpr.get(2)))
      else if head == "do":
        when is-empty(sexpr.rest):
          raise("Paret: do blocks cannot be empty")
        end
        doE(map(convert, sexpr.rest))
      else if head == "fun":
        lamE(check-params(sexpr.get(1)), convert(sexpr.get(2)))
      else if head == "+":
        bopE(plus, convert(sexpr.get(1)), convert(sexpr.get(2)))
      else if head == "-":
        bopE(minus, convert(sexpr.get(1)), convert(sexpr.get(2)))
      else if head == "++":
        bopE(append, convert(sexpr.get(1)), convert(sexpr.get(2)))
      else if head == "==":
        bopE(str-eq, convert(sexpr.get(1)), convert(sexpr.get(2)))
      else:
        func = convert(head)
        args = map(convert, sexpr.rest)
        appE(func, args)
      end
    else if Number(sexpr):
      numE(sexpr)
    else if String(sexpr):
      idE(sexpr)
    end
  end
  convert(prog)
end



############################# HELPER FUNCTION #############################

fun do-operation(op :: Operator, left :: Value, right :: Value) -> Value:
  cases (Operator) op:
    | plus =>
      cases (Value) left:
        | funV(_, _, _) => raise("illegal operand")
        | strV(_) => raise("illegal operand")
        | numV(n) => n
      end
      cases (Value) right:
        | funV(_, _, _) => raise("illegal operand")
        | strV(_) => raise("illegal operand")
        | numV(n) => numV(left.value + right.value)
      end
    | minus =>
      cases (Value) left:
        | funV(_, _, _) => raise("illegal operand")
        | strV(_) => raise("illegal operand")
        | numV(n) => n
      end
      cases (Value) right:
        | funV(_, _, _) => raise("illegal operand")
        | strV(_) => raise("illegal operand")
        | numV(n) => numV(left.value - right.value)
      end
    | append =>
      cases (Value) left:
        | funV(_, _, _) => raise("illegal operand")
        | numV(_) => raise("illegal operand")
        | strV(s) => s
      end
      cases (Value) right:
        | funV(_, _, _) => raise("illegal operand")
        | numV(_) => raise("illegal operand")
        | strV(n) => strV(left.value + right.value)
      end
    | str-eq =>
      cases (Value) left:
        | funV(_, _, _) => raise("illegal operand")
        | numV(_) => raise("illegal operand")
        | strV(s) => s
      end
      cases (Value) right:
        | funV(_, _, _) => raise("illegal operand")
        | numV(_) => raise("illegal operand")
        | strV(n) =>
          if left.value.contains(right.value) and right.value.contains(left.value):
            numV(1)
          else:
            numV(0)
          end
      end
  end
end

fun lookup(s :: String, env :: Env) -> String:
  cases (Env) env:
    | mt-env => raise("unbound identifier: " + s)
    | an-env(fn, v, e) =>
        if s == fn:
          v
        else:
          lookup(s, e)
        end
  end
end

fun fetch(n :: String, st :: Store) -> Value:
  cases (Store) st:
    | mt-store => raise("unknown location: " + n)
    | a-store(lo, v, s) =>
      if n == lo:
        v
      else:
        fetch(n, s)
      end
  end
end

 
 fun interp-args(
        args :: List<String>,
        params :: List<String>,
        env :: Env,
        store :: Store) -> Env:

   cases (List<String>) args:
     | empty =>
       cases (List<String>) params:
         | link(_, _) => raise("arity mismatch")
         | empty => mt-env
       end
     | link(ae, a-nxt) =>
       cases (List<String>) params:
         | empty => raise("arity mismatch")
         | link(an, p-nxt) =>
           arg-ret = interp-full(ae, env, store)
           arg-sto = arg-ret.store
           arg-val = arg-ret.val
           arg-loc = gensym("loc:")
           an-env(an,
                  arg-loc, 
                  interp-args(a-nxt, p-nxt, 
#                              an-env(an, arg-loc, env),
                              env,
                              a-store(arg-loc, arg-val, arg-sto)))
       end
   end
 end
# 
# # fun local-subst-list(with :: Expr, at :: String, lin :: 
# 
# fun local-subst(with :: Expr, at :: String, in :: Expr) -> Expr:
#   cases (Expr) in:
#     | numE(n) =>
#       in
#     | strE(s) =>
#       in
#     | idE(s) =>
#       if s == at:
#         with
#       else:
#         in
#       end
#     | bopE(op, left, right) =>
#       bopE(op, local-subst(with, at, left), local-subst(with, at, right))
#     | appE(f, al) =>
#       appE(f, local-subst(with, at, al))
#     | cifE(c, sq, alt) =>
#       cifE(local-subst(with, at, c), local-subst(with, at, sq), local-subst(with, at, alt))
#   end
# end
# 
# 


############################## ENTRANCE ###############################


fun eval(prog :: String) -> Value:
  interp(parse(read-sexpr(prog)))
end

fun interp(prog :: Expr) -> Value:
  interp-full(prog, mt-env, mt-store).val
end

fun interp-full(prog :: Expr, env :: Env, store :: Store) -> Result:
  cases (Expr) prog:
    | numE(n) =>
      result(numV(n), store)
    | strE(s) =>
      result(strV(s), store)
    | lamE(plst, bd) =>
      result(funV(plst, bd, env), store)
    | bopE(op, l, r) =>
      lv = interp-full(l, env, store)
      rv = interp-full(r, env, lv.store)
      result(do-operation(op, lv.val, rv.val), rv.store)
    | idE(s) =>
      result(fetch(lookup(s, env), store), store)
    | appE(f, al) =>
      interp-full(f.body, interp-args(al, f.params, env, store), store)
#    | cifE(c, sq, alt) =>
#      if interp-env(c, env).value <> 0:
#        interp-env(sq, env)
#      else:
#        interp-env(alt, env)
#      end
#    | letE(n, e, body) =>
#      interp-full(local-subst(e, n, body), env)
  end

where:
  eval('5') is numV(5)
  eval('"My name is parat"') is strV("My name is parat")

  eval('(+ 3 3)') is numV(6)

  eval('(+ "hello " "world")') raises "illegal operand"
  eval('(+ 3 "world")') raises "illegal operand"
  eval('(+ "Hello" 9)') raises "illegal operand"
  eval('(+ 3 (fun (x y) (+ x y)))') raises "illegal operand"
  eval('(+ (fun (x y) (+ x y)) 3)') raises "illegal operand"
  eval('(- 3 3)') is numV(0)
  eval('(- "hello " "world")') raises "illegal operand"
  eval('(- 3 "world")') raises "illegal operand"
  eval('(- "Hello" 9)') raises "illegal operand"
  eval('(- 3 (fun (x y) (+ x y)))') raises "illegal operand"
  eval('(- (fun (x y) (+ x y)) 3)') raises "illegal operand"

  eval('(++ "hello " "world")') is strV("hello world")
  eval('(++ "hello " 8)') raises "illegal operand"
  eval('(++ 8 "hello")') raises "illegal operand"
  eval('(++ 6 9)') raises "illegal operand"
  eval('(++ "hello" (fun (x y) (+ x y)))') raises "illegal operand"
  eval('(++ (fun (x y) (+ x y)) "hello")') raises "illegal operand"
  eval('(== "hello" "hello")') is numV(1)
  eval('(== "hello" "bybye")') is numV(0)
  eval('(== "hello" 1)') raises "illegal operand"
  eval('(== 1 "hello")') raises "illegal operand"
  eval('(== "hello" (fun (x y) (+ x y)))') raises "illegal operand"
  eval('(== (fun (x y) (+ x y)) "hello")') raises "illegal operand"

  eval('non-existent-id') raises "unbound identifier: non-existent-id"

#  eval('(let (x 3) (+ x 1))') is numV(4)

  eval('((fun () (+ 1 2)))')
    is numV(3)
  eval('((fun (x) (+ x 1)) 3)')
    is numV(4)
#  eval('((fun (x y) (+ x y)) 3 7)')
#    is numV(10)
#  eval('((fun (x y) (+ x y)) )')
#    raises "arity mismatch"
#  eval('((fun (x y) (+ x y)) 3)')
#    raises "arity mismatch"
#  eval('((fun (x y) (+ x y)) 3 7 9)')
#    raises "arity mismatch"
#  eval('((fun (x y) (+ x y)) 3 m)')
#    raises "unbound identifier: m"
#  eval('((fun (x y) x) 3 7)')
#    is numV(3)
#  eval('((fun (x y) (fun (m n) (* m n))) 3 7)')
#    is funV(["m", "n"], appE(idE("*"), [idE("m"), idE("n")]), an-env("x", numV(3), an-env("y", numV(7), mt-env)))

#  eval('((fun (x y) (fun (x y) (* x y))) 3 7)')
#    is funV(["x", "y"], appE(idE("*"), [idE("x"), idE("y")]), an-env("x", numV(3), an-env("y", numV(7), mt-env)))
#  eval('((fun (x y) ((fun (x y) (+ x y)) 1 1)) 3 7)')
#    is numV(2)

#  eval('(if 1 "yes" "no")') is strV("yes") 
#  eval('(if 0 "yes" "no")') is strV("no") 
#  eval('(if "str cond" "yes" "no")') is strV("yes") 
#
#  eval('(let (x 3) (+ x 3))') is numV(6)
#  eval('(let (tempting-lp (fun () (3))) (tempting-lp ())') is numV(3)
#  
end
