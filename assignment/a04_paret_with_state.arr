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

fun eval(prog :: String) -> Value:
  interp(parse(read-sexpr(prog)))
end

fun interp(prog :: Expr) -> Value:
  interp-full(prog, mt-env, mt-store).val
end

fun interp-full(prog :: Expr, env :: Env, store :: Store) -> Result:
  ##
  # Helper Functions: lookup
  #
  #   To get the location for a specific identifier from the 
  #   environment list; raises exception if couldn't find it.
  fun lookup(lkp-s :: String, lkp-env :: Env) -> String:
    cases (Env) lkp-env:
      | mt-env => raise("unbound identifier: " + lkp-s)
      | an-env(fn, v, e) =>
          if lkp-s == fn:
            v
          else:
            lookup(lkp-s, e)
          end
    end
  end
  ##
  # Helper Functions: fetch
  #
  #   To get the value from a specific location "address" from
  #   the storage list; raises exception if couldn't find it.
  #   The latest/inner-most assigning for a specific identifier
  #   should be the one closest to the front of the list.
  fun fetch(n :: String, ft-st :: Store) -> Value:
    cases (Store) ft-st:
      | mt-store => raise("unknown location: " + n)
      | a-store(lo, v, s) =>
        if n == lo:
          v
        else:
          fetch(n, s)
        end
    end
  end
  ##
  # Helper Functions: do-operation
  #
  #   To do the binary operation for the left value and right value
  #   which are both evaluated before calling this; Would raise
  #   illegal operand exception if (1) these two parameters are not
  #   of the same class of value, (2) wrong operand is passed for
  #   an operator.
  #
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
            if left.value == right.value:
              numV(1)
            else:
              numV(0)
            end
        end
    end
  end
  ##
  # Helper Functions: interp-args
  #
  #   This function would update the environment passing in and pop the result up
  #   to the caller ('interp-full' in the end). Repeatedly thread the store from 
  #   the head of the arg/param list to the end.   
  #
  fun interp-args(
         args :: List<String>,
         params :: List<String>,
         h-arg-env :: Env,
         h-arg-store :: Store):
    cases (List<String>) args:
      | empty =>
        cases (List<String>) params:
          | link(_, _) => raise("arity mismatch")
          | empty => {e : mt-env, sto : mt-store}
        end
      | link(ae, a-nxt) =>
        cases (List<String>) params:
          | empty => raise("arity mismatch")
          | link(an, p-nxt) =>
            arg-ret = interp-full(ae, h-arg-env, h-arg-store)
            arg-sto = arg-ret.store
            arg-val = arg-ret.val
            arg-loc = gensym("loc:")
            next-ret = interp-args(a-nxt, p-nxt, h-arg-env, arg-sto)
            {e : an-env(an, arg-loc, next-ret.e),
             sto : a-store(arg-loc, arg-val, next-ret.sto)}
        end
    end
  end
  ##
  # Helper Functions: do-helper
  #
  #   This function evaluate an expression sequence. It would thread the store from
  #   the head expression to the end repeatedly.
  #
  fun do-helper(e-l :: List<Expr>, env-do :: Env, store-do :: Store) -> Result:
    cases (List<Expr>) e-l:
      | empty => empty
      | link(exp, nxt-l) =>
        exp-ret = interp-full(exp, env-do, store-do)
        if nxt-l.length() == 0:
          exp-ret
        else:
          do-helper(nxt-l, env-do, exp-ret.store)
        end
    end
  end
  ##
  # Entrance of interp-full
  #
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
    | appE(f, arg-l) =>
      cases (Expr) f:
        | lamE(_, _) =>
          app-ret = interp-full(f, env, store)
          app-val = app-ret.val
          app-sto = app-ret.store
          arg-ret = interp-args(arg-l, app-val.params, env, app-sto)
          interp-full(app-val.body, arg-ret.e, arg-ret.sto)
        | idE(_) =>
          app-ret = interp-full(f, env, store)
          app-val = app-ret.val
          app-sto = app-ret.store
          arg-ret = interp-args(arg-l, app-val.params, env, app-sto)
          interp-full(app-val.body, arg-ret.e, arg-ret.sto)
      end
    | cifE(c, sq, alt) =>
      cond-ret = interp-full(c, env, store)
      seqr-ret = interp-full(sq, env, cond-ret.store)
      altr-ret = interp-full(alt, env, seqr-ret.store)
      if cond-ret.val == numV(1):
        seqr-ret
      else:
        altr-ret
      end
    | letE(id, exp, bdy) =>
      exp-ret = interp-full(exp, env, store)
      id-loc = gensym("loc:")
      interp-full(bdy,
                  an-env(id, id-loc, env),
                  a-store(id-loc, exp-ret.val, exp-ret.store))
    | assignE(n, exp) =>
      var-loc = lookup(n, env)
      new-ret = interp-full(exp, env, store)
      result(new-ret.val, a-store(var-loc, new-ret.val, new-ret.store))
    | doE(exp-l) =>
      do-helper(exp-l, env, store)
  end

where:
  fun len-for-test(l :: List) -> Number:
    cases(List) l:
      | empty => 0
      | link(f, r) => 1 + len-for-test(r)
    end
  where:
    len-for-test(empty) is 0
    len-for-test(link(1, empty)) is 1
    len-for-test(link(1, link(2, empty))) is 2
  end
  #######################################################
  # Values
  #
  eval('5') is numV(5)
  eval('"My name is parat"') is strV("My name is parat")

  eval('(fun () (3))').params.length() is 0
  eval('(fun () (3))').body is appE(numE(3), [])
  eval('(fun () (3))').env is mt-env

  eval('(fun (x y) (+ x y))').params.length() is 2
  eval('(fun (x y) (+ x y))').body is bopE(plus, idE("x"), idE("y"))
  eval('(fun (x y) (+ x y))').env is mt-env

  eval('(fun (x y) (+ x (+ y z)))').params.length() is 2
  eval('(fun (x y) (+ x (+ y z)))').body is bopE(plus, idE("x"), bopE(plus, idE("y"), idE("z")))
  eval('(fun (x y) (+ x (+ y z)))').env is mt-env
  #######################################################
  # Binary Operation
  #
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
  #######################################################
  # Identifier, Lambda and Trivial Application
  #
  eval('
    non-existent-id
  ') raises "unbound identifier: non-existent-id"
  eval('
    ((fun () (+ 1 2)))
  ') is numV(3)
  eval('
    ((fun (x) (+ x 1)) 3)
  ') is numV(4)
  eval('
    ((fun (x y) (+ x y)) 3 7)
  ') is numV(10)
  eval('
    ((fun (x y) (+ x y)) )
  ') raises "arity mismatch"
  eval('
    ((fun (x y) (+ x y)) 3)
  ') raises "arity mismatch"
  eval('
    ((fun (x y) (+ x y)) 3 7 9)
  ') raises "arity mismatch"
  eval('
    ((fun (x y) (+ x y)) 3 m)
  ') raises "unbound identifier: m"
  eval('
    ((fun (x y) x) 3 7)
  ') is numV(3)
  eval('
    ((fun (x y)
        (if (== x y) 1 0))
        "hello" "hello")
  ') is numV(1)
  eval('
    ((fun (x y)
        (if (== x y) 1 0))
        "goodbye" "hello")
  ') is numV(0)
  eval('
    ((fun (x y)
        ((fun (x y)
            (+ x y)) 1 1)) 3 7)')
    is numV(2)
  #######################################################
  # Local Binding (w/ or w/o Application)
  #   & Sequences & Stateful Assign Operation
  #
  eval('
    (do (+ 1 1))
  ') 2
  eval('
    (do (++ "hello " "world"))
  ') strV("hello world")
  eval('
    (do (+ x 1))
  ') raises "unbound identifier: x"
  eval('
    (let (x 3) (+ x 1))
  ') is numV(4)
  eval('
    (let (x 1) (assign x 2))
  ') is numV(2)
  eval('
    (let (x unbound-id) (assign x 2))
  ') raises "unbound identifier: unbound-id"
  eval('
    (let 
      (tempting-lp (fun () (tempting-lp)))
      (tempting-lp))
  ') raises "unbound identifier: tempting-lp"
  eval('
    (let (x 1) 
      (do (+ x 1)
          (+ x 1)))
  ') is numV(2)
  eval('
    (let (x 1) 
      (do (assign x 9)
          (+ x 1)))
  ') is numV(10)
  eval('
    (let (x 1) 
      (do (assign x 9)
          (+ x (+ x x))))
  ') is numV(27)
  #######################################################
  # Compound case involving stateful assign operation
  # in application's arguments.
  #
  eval('
    (let (x 1) 
      ((fun (a1 a2 a3) (+ a1 (- a2 a3)))
          (do (assign x 9)
            (+ x (+ x x)))
          (- x 10)
          (+ x 10)))
  ') is numV(7)
  #######################################################
  # Refer to a function identifier as application 
  # 
  eval('
    (let
      (my-fun-id
            (fun (fx fy fz) (+ fz (+ fx fy))))
      (let (x 0)
          (do (assign x (my-fun-id 1 2 3))
              (+ x (+ x x)))))
  ') is numV(18)
end
