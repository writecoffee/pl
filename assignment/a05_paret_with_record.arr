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
  fun field-helper(fields :: List<Field>, f-env :: Env, f-store :: Store):
    cases (List<Field>) fields:
      | empty =>
        {fv-l : [], sto : f-store}
      | link(fe, nxt) =>
        e-ret = interp-full(fe.value, f-env, f-store)
        e-val = e-ret.val
        e-sto = e-ret.store
        nxt-ret = field-helper(nxt, f-env, e-sto)
        nxt-val = nxt-ret.fv-l
        nxt-sto = nxt-ret.sto
        {fv-l : [fieldV(fe.name, e-val)] + nxt-val, sto : nxt-sto}
    end
  end
  fun lookup-field-helper(lkp-f-fn :: String, lkp-f-l :: List<FieldV>) -> FieldV:
    cases (List<FieldV>) lkp-f-l:
      | empty =>
        raise("cannot find: " + lkp-f-fn + " in record")
      | link(f, f-l-nxt) =>
        if f.name == lkp-f-fn:
          f
        else:
          lookup-field-helper(lkp-f-fn, f-l-nxt)
        end
    end
  end
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
        | letE(id, iv, body) =>
          cases (Expr) body:
            | lamE(lp-l, lbd) =>
              iv-ret = interp-full(iv, env, store)
              iv-val = iv-ret.val
              iv-sto = iv-ret.store
              arg-ret = interp-args(arg-l, lp-l, env, iv-sto)
              id-loc = gensym("loc:")
              interp-full(lbd,
                          an-env(id, id-loc, arg-ret.e),
                          a-store(id-loc, iv-val, arg-ret.sto))
            | else =>
              raise("invalid lambda expresion")
          end
        | else =>
          raise("invalid function expression for evaluation")
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
    | assignE(id, exp) =>
      var-loc = lookup(id, env)
      new-ret = interp-full(exp, env, store)
      result(new-ret.val, a-store(var-loc, new-ret.val, new-ret.store))
    | doE(exp-l) =>
      do-helper(exp-l, env, store)
    | recordE(f-l) =>
      f-l-ret = field-helper(f-l, env, store)
      result(recV(f-l-ret.fv-l), f-l-ret.sto)
    | lookupE(r-e, fn) =>
      cases (Expr) r-e:
        | recordE(_) =>
          rec-ret = interp-full(r-e, env, store)
          result(lookup-field-helper(fn, rec-ret.val.fields).value, rec-ret.store)
        | idE(id) =>
          ide-ret = interp-full(r-e, env, store)
          ide-val = ide-ret.val
          ide-sto = ide-ret.store
          cases (Value) ide-val:
            | recV(f-l) =>
              result(lookup-field-helper(fn, f-l).value, ide-sto)
            | else => 
              raise("lookupE: the Id: " + fn + " cannot be evaluated to a record value")
          end
        | assignE(id, exp) =>
          asn-ret = interp-full(r-e, env, store)
          asn-val = asn-ret.val
          asn-sto = asn-sto.store
          cases (Value) asn-val:
            | recV(f-l) =>
              result(lookup-field-helper(fn, f-l).value, asn-sto)
            | else => 
              raise("lookupE: the Id: " + fn + " cannot be evaluated to a record value")
          end
        | else =>
          print(r-e)
          raise("lookupE: the expression cannot be evaluated to a record value")
      end
    | extendE(r-e, fn, nv) =>
      cases (Expr) r-e:
        | recordE(_) =>
          rec-ret = interp-full(r-e, env, store)
          nv-ret = interp-full(nv, env, rec-ret.store)
          result(recV([fieldV(fn, nv-ret.val)] + rec-ret.val.fields), nv-ret.store)
        | else =>
          raise("extendE: the rec cannot be evaluated to a record value")
       end
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
  # Application
  eval("
    ((let (x 1)
      (fun (y) (+ x y))) 5)
  ") is numV(6)
  #######################################################
  # Records
  eval('
    (record (x 1) (y 3))
  ') is recV([fieldV("x", numV(1)), fieldV("y", numV(3))])
  eval('
    (lookup (record (x 1) (y 3)) x)
  ') is numV(1)
  eval('
    (extend (record (x 1) (y 3)) z 9)
  ') is recV([fieldV("z", numV(9)), fieldV("x", numV(1)), fieldV("y", numV(3))])
  eval('
    (extend (record (x 1) (y 3)) x 9)
  ') is recV([fieldV("x", numV(9)), fieldV("x", numV(1)), fieldV("y", numV(3))])
  eval('
    (extend (record (x 1) (y 3)) x 9)
  ') is recV([fieldV("x", numV(9)), fieldV("x", numV(1)), fieldV("y", numV(3))])
  eval('
    (let (my-record (record (x 1) (y 3)))
      ((fun (a1 a2 a3) (+ a1 (- a2 a3)))
          (do (assign my-record (record (x 99) (y 999)))
              (lookup my-record x))
          0 0))
  ') is numV(99)
  eval('
    (let (my-record (record (x 1) (y 3)))
      ((fun (a1 a2 a3) (+ a1 (- a2 a3)))
          (do (assign my-record (record (x 99) (y 999)))
              (+ (lookup my-record x) 
                 (+ (lookup (assign my-record (record (x 0) (y 0))) x)
                    (lookup my-record y))))
          0 0))
  ') is numV(99)

end
