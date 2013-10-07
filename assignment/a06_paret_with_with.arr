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
  # Helper Function: with-helper
  #
  # Allocate new environment and store slot for the field list,
  # padding them at the head of the environment and store list.
  # It will return a new environment and store list that is a
  # concatentation of the field list passing in and the original
  # environment and store
  fun with-helper(fields :: List<FieldV>, w-env :: Env, w-sto :: Store):
    cases (List<FieldV>) fields:
      | empty => 
        { env : w-env,
          sto : w-sto }
      | link(fv, nxt-f-l) =>
        fd-loc = gensym("loc:")
        nxt-ret = with-helper(nxt-f-l, w-env, w-sto)
        nxt-env = nxt-ret.env
        nxt-sto = nxt-ret.sto
        { env : an-env(fv.name, fd-loc, nxt-env),
          sto : a-store(fd-loc, fv.value, nxt-sto) }
    end
  end
  ##
  # Helper Function: concat-env
  # 
  #   Used for concatinating two environment, the first one 
  #   would shadow the second one; called by interp-full::appE 
  #   when we do "let" to extend the environment for the lambda 
  #   body and evaluate the application body later on together
  #   with the argment passing in
  fun concat-env(env1 :: Env, env2 :: Env) -> Env:
    cases (Env) env1:
      | mt-env =>
        env2
      | an-env(e1-n, e1-l, e1-ext) =>
        an-env(e1-n, e1-l, concat-env(e1-ext, env2))
    end
  end
  ##
  # Helper Function: field-helper
  # 
  #   To evaluate a list of expression which would be 
  #   evaluated as field value eventually. Return the field
  #   list as well as the store modified by then
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
  ##
  # Helper Function: lookup-field-helper
  # 
  #   To lookup a field value in the field list by referring to 
  #   their field name with the 'key'
  fun lookup-field-helper(lkp-f-fn :: String, lkp-f-l :: List<FieldV>) -> FieldV:
    cases (List<FieldV>) lkp-f-l:
      | empty =>
        raise("record field: " + lkp-f-fn + " not found")
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
          | empty => {e : h-arg-env, sto : h-arg-store}
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
      | link(exp, nxt-l) =>
        exp-ret = interp-full(exp, env-do, store-do)
        if nxt-l.length() == 0:
          exp-ret
        else:
          do-helper(nxt-l, env-do, exp-ret.store)
        end
      | else =>
        raise("doE: cannot pass an empty expression list!")
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
        | else =>
          oe-ret = interp-full(f, env, store)
          oe-val = oe-ret.val
          oe-sto = oe-ret.store
          cases (Value) oe-val:
            | funV(f-p-l, f-b, f-env) =>
              arg-ret = interp-args(arg-l, f-p-l, concat-env(f-env, env), oe-sto)
              interp-full(f-b, arg-ret.e, arg-ret.sto)
            | else =>
              raise("appE: " + f + " cannot be evaluated to a function value")
          end
      end
    | cifE(c, sq, alt) =>
      cond-ret = interp-full(c, env, store)
      cond-val = cond-ret.val
      cond-sto = cond-ret.store
      if cond-val == numV(1):
        interp-full(sq, env, cond-sto)
      else:
        interp-full(alt, env, cond-sto)
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
          rec-val = rec-ret.val
          rec-sto = rec-ret.store
          result(lookup-field-helper(fn, rec-val.fields).value, rec-ret.store)
        | else =>
          oe-ret = interp-full(r-e, env, store)
          oe-val = oe-ret.val
          oe-sto = oe-ret.store
          cases (Value) oe-val:
            | recV(f-l) =>
              result(lookup-field-helper(fn, f-l).value, oe-sto)
            | else =>
              raise("lookupE: input cannot be evaluated to a record value")
          end
      end
    | extendE(r-e, fn, nv) =>
      cases (Expr) r-e:
        | recordE(_) =>
          rec-ret = interp-full(r-e, env, store)
          nv-ret = interp-full(nv, env, rec-ret.store)
          result(recV([fieldV(fn, nv-ret.val)] + rec-ret.val.fields), nv-ret.store)
        | else =>
          oe-ret = interp-full(r-e, env, store)
          oe-val = oe-ret.val
          oe-sto = oe-ret.store
          cases (Value) oe-val:
            | recV(f-l) =>
              nv-ret = interp-full(nv, env, oe-sto)
              nv-val = nv-ret.val
              nv-sto = nv-ret.store
              result(recV([fieldV(fn, nv-val)] + f-l), nv-sto)
            | else =>
              raise("extendE: input cannot be evaluated to a record value")
          end
       end
    | withE(ns, bdy) =>
      cases (Expr) ns:
        | recordE(_) =>
          ns-ret = interp-full(ns, env, store)
          ns-val = ns-ret.val
          ns-sto = ns-ret.store
          new-ret = with-helper(ns-val.fields, env, ns-sto)
          new-env = new-ret.env
          new-sto = new-ret.sto
          interp-full(bdy, new-env, new-sto)
        | else =>
          oe-ret = interp-full(ns, env, store)
          oe-val = oe-ret.val
          oe-sto = oe-ret.store
          cases (Value) oe-val:
            | recV(f-l) =>
              new-ret = with-helper(f-l, env, oe-sto)
              new-env = new-ret.env
              new-sto = new-ret.sto
              interp-full(bdy, new-env, new-sto)
            | else =>
              raise("withE: the namespace cannot be evaluated to a record value")
          end
      end
  end
where:
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
  eval('(+ "hello " "world")') raises ""
  eval('(+ 3 "world")') raises ""
  eval('(+ "Hello" 9)') raises ""
  eval('(+ 3 (fun (x y) (+ x y)))') raises ""
  eval('(+ (fun (x y) (+ x y)) 3)') raises ""
  eval('(- 3 3)') is numV(0)
  eval('(- "hello " "world")') raises ""
  eval('(- 3 "world")') raises ""
  eval('(- "Hello" 9)') raises ""
  eval('(- 3 (fun (x y) (+ x y)))') raises ""
  eval('(- (fun (x y) (+ x y)) 3)') raises ""
  eval('(++ "hello " "world")') is strV("hello world")
  eval('(++ "hello " 8)') raises ""
  eval('(++ 8 "hello")') raises ""
  eval('(++ 6 9)') raises ""
  eval('(++ "hello" (fun (x y) (+ x y)))') raises ""
  eval('(++ (fun (x y) (+ x y)) "hello")') raises ""
  eval('(== "hello" "hello")') is numV(1)
  eval('(== "hello" "bybye")') is numV(0)
  eval('(== "hello" 1)') raises ""
  eval('(== 1 "hello")') raises ""
  eval('(== "hello" (fun (x y) (+ x y)))') raises ""
  eval('(== (fun (x y) (+ x y)) "hello")') raises ""
  #######################################################
  # Identifier, Lambda and Trivial Application
  #
  eval('
    non-existent-id
  ') raises "" # "unbound identifier: non-existent-id"
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
  ') raises "" # "arity mismatch"
  eval('
    ((fun (x y) (+ x y)) 3)
  ') raises "" # "arity mismatch"
  eval('
    ((fun (x y) (+ x y)) 3 7 9)
  ') raises "" # "arity mismatch"
  eval('
    ((fun (x y) (+ x y)) 3 m)
  ') raises "" # "unbound identifier: m"
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
  ') raises "" # "unbound identifier: x"
  eval('
    (let (x 3) (+ x 1))
  ') is numV(4)
  eval('
    (let (x 1) (assign x 2))
  ') is numV(2)
  eval('
    (let (x unbound-id) (assign x 2))
  ') raises "" # "unbound identifier: unbound-id"
#  eval('
#    (let 
#      (tempting-lp (fun () (tempting-lp)))
#      (tempting-lp))
#  ') raises "unbound identifier: tempting-lp"
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
  eval('
    (let (x 1) 
      ((fun (a1 a2 a3) (+ a1 (- a2 a3)))
          (do (assign x 9)
            (+ x (+ x x)))
          (- x 10)
          (+ x 10)))
  ') is numV(7)
  eval('
    (let
      (my-fun-id
            (fun (fx fy fz) (+ fz (+ fx fy))))
      (let (x 0)
          (do (assign x (my-fun-id 1 2 3))
              (+ x (+ x x)))))
  ') is numV(18)
  eval('
    ((let (x 1)
      (fun (y) (+ x y))) 5)
  ') is numV(6)
  eval('
    (let (myFunc (fun (x) (assign x 1)))
      (let (y 0)
        (do (myFunc y) y)))
  ') is numV(0)
 #######################################################
 # Records
  eval('
    (lookup (record (x 1) (y 3)) x)
  ') is numV(1)
  eval('
    (let (my-record (record (x 1) (y 3)))
         (lookup (extend my-record z 9) z))
  ') is numV(9)
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
  eval('
    (let (my-record (record (x 1) (y 3)))
      ((fun (a1 a2 a3) (+ a1 (- a2 a3)))
          (lookup my-record y)
          (lookup my-record x)
          (do (assign my-record (record (x 99) (y 999)))
              (+ (lookup (extend my-record x 0) x)
                 (+ (lookup (assign my-record (record (x -1) (y 0))) x)
                    (lookup my-record y))))))
  ') is numV(5)
  eval('
    (lookup (record (x 1) (y 3)) not-exist-id)
  ') raises "" # "record field: not-exist-id not found"
  eval('
    (lookup (fun () 3) not-exist-id)
  ') raises "" # "lookupE: input cannot be evaluated to a record value"
  eval('
    (let (my-record (record (x 1) (y 3)))
         (lookup (extend (fun () 3) z 9) z))
  ') raises "" # "extendE: input cannot be evaluated to a record value"
  #######################################################
  # With
  #
  eval('
    (with (record (x 1) (y 3)) x)
  ') is numV(1)
  eval('
    (let (x 1)
       (with (record (y 3)) (+ x y)))
  ') is numV(4)
  eval('
    (let (x 1)
       (with (record (x 3)) (+ x x)))
  ') is numV(6)
  eval('
    (let (x 1)
       (with (record (x 3)) (+ x x)))
  ') is numV(6)
  eval('
    (let (x 100)
      (let (my-record (record (x 1) (y 100)))
        ((fun (a1 a2 a3) (+ a1 (- a2 a3)))
            (with my-record x)
            (with my-record y)
            x)))
  ') is numV(1)
  eval('
    (let (x 100)
      (let (my-record (record (x 1) (y 100)))
        ((fun (a1 a2 a3) (+ a1 (- a2 a3)))
            (do (assign my-record (record (x 101) (y 999)))
                (with my-record x))
            (with my-record y)
            x)))
  ') is numV(1000)
  eval('
    (let (my-record (record (argX 1) (argY 10) (argZ 100)))
      (let (fun-set-record
              (fun (a1 a2 a3)
                   (record (x (- 0 a1))
                           (y (- 0 a2))
                           (z (- 0 a3)))))
           (with (fun-set-record
                    (lookup my-record argX)
                    (lookup my-record argY)
                    (lookup my-record argZ))
                 (+ x (+ y z)))))
  ') is numV(-111)
  eval('
    ((let
        (my-record (record (argX 1) (argY 10) (argZ 100)))
        (fun (choice base)
             (if (== choice "c1")
                 (- base (lookup my-record argX))
                 (if (== choice "c2")
                     (- base (lookup my-record argY))
                     (if == choice "c3")
                       (- base (lookup my-record argZ))
                       ("UNKNOWN CHOICE")))))
      "c2" 0)
  ') is numV(-10)
  eval('
    ((let
        (my-record (record (argX 1) (argY 10) (argZ 100)))
        (fun (choice base)
             (if (== choice (do (extend my-record argX -1)
                                "c1"))
                 (- base (lookup my-record argX))
                 (if (== choice "c2")
                     (- base (lookup my-record argX))
                     (if == choice "c3")
                       (- base (lookup my-record argZ))
                       ("UNKNOWN CHOICE")))))
      "c2" 0)
  ') is numV(-1)
  eval('
    ((let
        (my-record (record (argX 1) (argY 10) (argZ 100)))
        (fun (choice base)
             (if (== choice "c1")
                 (with (extend my-record argX -1) (- base argX))
                 (if (== choice "c2")
                     (- base (lookup my-record argY))
                     (if == choice "c3")
                       (- base (lookup my-record argZ))
                       ("UNKNOWN CHOICE")))))
      "c1" 0)
  ') is numV(1)
  eval('
    (let (x 100)
      (let (my-record (record (x 1) (y 100)))
        ((fun (a1 a2 a3) (+ a1 (- a2 a3)))
            (with "hello, I am not a recV" x)
            (with my-record y)
            x)))
  ') raises "" # "withE: the namespace cannot be evaluated to a record value"
  eval('
    (let (outmostId 100)
      (let (my-record (record (x 1) (y 100)))
        ((fun (a1 a2 a3) (+ a1 (- a2 a3)))
            (with my-record z)
            (with my-record y)
            outmostId)))
  ') raises "" # "unbound identifier: z"
end
