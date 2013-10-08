#lang pyret/whalesong

data Value:
  | numV(value :: Number)
  | strV(value :: String)
  | funV(params :: List<String>, body :: Expr, env :: Env)
  | recV(fields :: List<FieldV>)
end

data FieldV:
  | fieldV(name :: String, value :: Value)
end

data Env:
  | mt-env
  | an-env(name :: String, loc :: String, env :: Env)
end

data Store:
  | mt-store
  | a-store(loc :: String, val :: Value, store :: Store)
end

data Result:
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
  | recordE(fields :: List<Field>)
  | lookupE(rec :: Expr, field-name :: String)
  | extendE(rec :: Expr, field-name :: String, new-value :: Expr)
  | withE(namespace :: Expr, body :: Expr)

  | holeE
end

data Field:
  | fieldE(name :: String, value :: Expr)
end

data Operator:
  | plus
  | minus
  | append
  | str-eq
end


fun parse(prog) -> Expr:
  fun convert-field(sexpr):
    fieldE(sexpr.get(0), convert(sexpr.get(1)))
  end
  fun convert(sexpr):
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
      else if head == "record":
        recordE(map(convert-field, sexpr.rest))
      else if head == "lookup":
        lookupE(convert(sexpr.get(1)), sexpr.get(2))
      else if head == "extend":
        extendE(convert(sexpr.get(1)),
                sexpr.get(2),
                convert(sexpr.get(3)))
      else if head == "with":
        withE(convert(sexpr.get(1)), convert(sexpr.get(2)))
      else if head == "assign":
        assignE(sexpr.get(1), convert(sexpr.get(2)))
      else if head == "do":
        when is-empty(sexpr.rest):
          raise("Paret: do blocks cannot be empty")
        end
        doE(map(convert, sexpr.rest))
      else if head == "fun":
        lamE(sexpr.get(1), convert(sexpr.get(2)))
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
    else if sexpr == "@":
      holeE
    else if String(sexpr):
      idE(sexpr)
    end
  end
  convert(prog)
end

fun parse-and-calculate-locals(prog :: String) -> Set<String>:
  calculate-locals(parse(read-sexpr(prog)))
end

parse-and-calc = parse-and-calculate-locals
fun calculate-locals(expr :: Expr) -> Set<String>:
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
    fun type-checking(t):
      if not (t(left) and t(right)):
        raise("illegal operand for operator: " + op)
      else:
        nothing
      end
    end
    cases (Operator) op:
      | plus =>
        type-checking(is-numV)
        numV(left.value + right.value)
      | minus =>
        type-checking(is-numV)
        numV(left.value - right.value)
      | append =>
        type-checking(is-strV)
        strV(left.value.append(right.value))
      | str-eq =>
        type-checking(is-strV)
        if left.value == right.value:
          numV(1)
        else:
          numV(0)
        end
    end
  end
  data Pid:
    | mt-pid
    | an-pid(name :: String, pid :: Pid)
  end
  data Prd:
    | mt-prd
    | an-prd(name :: String, fields :: Pid, Prd)
  end
  fun transfer-pid-2-set(t-pid :: Pid):
    cases (Pid) t-pid:
      | mt-pid =>
        set([])
      | an-pid(n, nxt) =>
        set([n]).union(transfer-pid-2-set(nxt))
    end
  end
  fun cal-while-interp(
      i-prog :: Expr,
      i-env :: Env,
      i-store :: Store,
      i-pid :: Pid,
      i-prd :: Prd):
    cases (Expr) i-prog:
      | holeE =>
        {
          res : nothing,
          pad : i-pid
        }
      | numE(n) =>
        {
          res : result(numV(n), i-store),
          pad : mt-pid
        }
      | strE(s) =>
        {
          res : result(strV(s), i-store),
          pad : mt-pid
        }
      | letE(id, exp, bd) =>
        exp-ret = cal-while-interp(exp, i-env, i-store, i-pid, i-prd)
        exp-res = exp-ret.res
        exp-pad = exp-ret.pad
        id-loc = gensym("loc:")
        if exp-res == nothing:
          {
            res : nothing,
            pad : exp-pad
          }
        else:
          cal-while-interp(
            bd,
            an-env(id, id-loc, i-env),
            a-store(id-loc, exp-res.val, exp-res.store),
            an-pid(id, i-pid),
            i-prd)
        end
      | bopE(op, l, r) =>
        lv-ret = cal-while-interp(l, i-env, i-store, i-pid, i-prd)
        lv-res = lv-ret.res
        lv-pad = lv-ret.pad
        if lv-res == nothing:
          {
            res : nothing,
            pad : lv-pad
          }
        else:
          rv-ret = cal-while-interp(r, i-env, lv-res.store, i-pid, i-prd)
          rv-res = rv-ret.res
          rv-pad = rv-ret.pad
          if rv-res == nothing:
            {
              res : nothing,
              pad : mt-pid
            }
          else:
            {
              res : result(do-operation(op, lv-res.val, rv-res.val), rv-res.store),
              pad : mt-pid
            }
          end
        end
    end
  end
  transfer-pid-2-set(cal-while-interp(expr, mt-env, mt-store, mt-pid, mt-prd).pad)
where:
  parse-and-calculate-locals('
    (let (x 1) @)
  ') is set(["x"])
  parse-and-calculate-locals('
    (let (x (+ 1 @)) x)
  ') is set([])
#  parse-and-calculate-locals('(@)')
#    is set([])
#  parse-and-calculate-locals('((fun (x) (x)) 4)')
#    is set([])
#  parse-and-calculate-locals('((fun (x) (@)) 4)')
#    is set(["x"])
#  parse-and-calculate-locals('
#    ((fun (m n)
#        (fun (x y z) (@)))
#        7 8)
#  ') is set(["x", "y", "z", "m", "n"])
#  parse-and-calculate-locals('
#    ((fun (m n)
#        (+ @ m))
#        7 8)
#  ') is set(["m", "n"])
#  parse-and-calculate-locals('
#    ((fun (x y z)
#        (@))
#        m)
#  ') is set(["x", "y", "z"])
#  parse-and-calculate-locals('
#    ((fun (x y)
#        (if (== x y) @ 0))
#        "hello" "hello")
#  ') is set(["x", "y"])
#  parse-and-calculate-locals('
#    ((fun (x y)
#        (if (== x y)
#            (fun (m n) (+ m @))
#            (fun (o p) (* o p))))
#        "hello" "hello")
#  ') is set(["x", "y", "m", "n"])
#  parse-and-calculate-locals('
#    ((fun (x y)
#        (let (m (+ x 3)) @)))
#  ') is set(["x", "y", "m"])
#  parse-and-calculate-locals('
#    ((fun (x y)
#        (let (m (+ @ 3)) (+ x y))))
#  ') is set(["x", "y"])
#  parse-and-calculate-locals('
#    ((fun (x y)
#        (let  (temp-var 0) 
#              (let (next-var @) "hello-end"))) 9 10)
#  ') is set(["x", "y", "temp-var"])
end
