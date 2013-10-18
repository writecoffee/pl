#lang pyret/whalesong

data Value:
  | numV(value :: Number)
  | strV(value :: String)
  | funV(params :: List<String>, body :: Block, env :: Env)
  | recV(fields :: List<FieldV>)
  | nullV
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

data Block:
  | block(stmts :: List<Stmt>)
end

data Stmt:
  | defvar(name :: String, expr :: Expr)
  | assign(name :: String, expr :: Expr)
  | expr-stmt(expr :: Expr)
end

data Expr:
  | nullE
  | idE(name :: String)
  | numE(value :: Number)
  | strE(value :: String)
  | bopE(op :: Operator, left :: Expr, right :: Expr)
  | cifE(cond :: Expr, consq :: Expr, altern :: Expr)
  | lamE(params :: List<String>, body :: Block)
  | appE(func :: Expr, args :: List<Expr>)

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

fun parse(prog) -> Block:
  fun convert-field(sexpr):
    fieldE(sexpr.get(0), convert(sexpr.get(1)))
  end

  fun convert-block(sexpr-list):
    block(map(convert-stmt, sexpr-list))
  end

  fun convert-stmt(sexpr):
    if List(sexpr):
      head = sexpr.first
      if head == "assign":
        assign(sexpr.get(1), convert(sexpr.get(2)))
      else if head == "defvar":
        defvar(sexpr.get(1), convert(sexpr.get(2)))
      else:
        expr-stmt(convert(sexpr))
      end
    else:
      expr-stmt(convert(sexpr))
    end
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
      else if head == "record":
        recordE(map(convert-field, sexpr.rest))
      else if head == "lookup":
        lookupE(convert(sexpr.get(1)), sexpr.get(2))
      else if head == "extend":
        extendE(convert(sexpr.get(1)),
                sexpr.get(2),
                convert(sexpr.get(3)))
      else if head == "fun":
        lamE(sexpr.get(1), convert-block(sexpr.rest.rest))
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
    else if sexpr == "null":
      nullE
    else if Number(sexpr):
      numE(sexpr)
    else if String(sexpr):
      idE(sexpr)
    end
  end

  convert-block(prog)
end

fun eval(prog :: String) -> Value:
  interp(parse(read-sexpr-list(prog)))
end

fun interp(prog :: Block) -> Value:
  interp-full(prog, mt-env, mt-store).val
end

fun interp-full(prog :: Block, env :: Env, store :: Store) -> Result:
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
        e-ret = interp-full-expr(fe.value, f-env, f-store)
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
  # Helper Functions: interp-full-expr-args
  #
  #   This function would update the environment passing in and pop 
  #   the result up to the caller ('interp-full' in the end).
  #   Repeatedly thread the store from the head of the arg/param
  #   list to the end.   
  #
  fun interp-full-expr-args(
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
            next-ret = interp-full-expr-args(a-nxt, p-nxt, h-arg-env, arg-sto)
            {e : an-env(an, arg-loc, next-ret.e),
             sto : a-store(arg-loc, arg-val, next-ret.sto)}
        end
    end
  end
  ##
  # interp-full-expr:
  #
  #   Interpret one specific expression at once. This is mostly 
  #   inherrited from previous assignments.
  #
  fun interp-full-expr(ie-expr :: Expr, ie-env :: Env, ie-store :: Store) -> Result:
    cases (Expr) ie-expr:
      | nullE =>
        result(nullV, ie-store)
      | numE(n) =>
        result(numV(n), ie-store)
      | strE(s) =>
        result(strV(s), ie-store)
      | lamE(p-l, blk) =>
        result(funV(p-l, blk, ie-env), ie-store)
      | recordE(f-l) =>
        f-l-ret = field-helper(f-l, ie-env, ie-store)
        result(recV(f-l-ret.fv-l), f-l-ret.sto)
      | bopE(op, l, r) =>
        lv = interp-full-expr(l, ie-env, ie-store)
        rv = interp-full-expr(r, ie-env, lv.store)
        result(do-operation(op, lv.val, rv.val), rv.store)
      | cifE(c, sq, alt) =>
        cond-ret = interp-full-expr(c, ie-env, ie-store)
        cond-val = cond-ret.val
        cond-sto = cond-ret.store
        if cond-val == numV(1):
          interp-full-expr(sq, ie-env, cond-sto)
        else:
          interp-full-expr(alt, ie-env, cond-sto)
        end
      | lookupE(r-e, fn) =>
        cases (Expr) r-e:
          | recordE(_) =>
            rec-ret = interp-full-expr(r-e, ie-env, ie-store)
            rec-val = rec-ret.val
            rec-sto = rec-ret.store
            result(lookup-field-helper(fn, rec-val.fields).value, rec-ret.store)
          | else =>
            oe-ret = interp-full-expr(r-e, ie-env, ie-store)
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
            rec-ret = interp-full-expr(r-e, ie-env, ie-store)
            nv-ret = interp-full-expr(nv, ie-env, rec-ret.store)
            result(recV([fieldV(fn, nv-ret.val)] + rec-ret.val.fields), nv-ret.store)
          | else =>
            oe-ret = interp-full-expr(r-e, ie-env, ie-store)
            oe-val = oe-ret.val
            oe-sto = oe-ret.store
            cases (Value) oe-val:
              | recV(f-l) =>
                nv-ret = interp-full-expr(nv, ie-env, oe-sto)
                nv-val = nv-ret.val
                nv-sto = nv-ret.store
                result(recV([fieldV(fn, nv-val)] + f-l), nv-sto)
              | else =>
                raise("extendE: input cannot be evaluated to a record value")
            end
        end
      | idE(s) =>
        result(fetch(lookup(s, ie-env), ie-store), ie-store)
      | appE(fun-e, arg-l) =>
        cases (Expr) fun-e:
          | lamE(_, _) =>
            app-ret = interp-full-expr(fun-e, ie-env, ie-store)
            app-val = app-ret.val
            app-sto = app-ret.store
            arg-ret = interp-full-expr-args(arg-l, app-val.params, ie-env, app-sto)
            interp-full-expr(app-val.body, arg-ret.e, arg-ret.sto)
          | else =>
            oe-ret = interp-full-expr(fun-e, ie-env, ie-store)
            oe-val = oe-ret.val
            oe-sto = oe-ret.store
            cases (Value) oe-val:
              | funV(f-p-l, f-b, f-env) =>
                arg-ret = interp-full-expr-args(
                             arg-l, f-p-l, concat-env(f-env, ie-env), oe-sto)
                interp-full(f-b, arg-ret.e, arg-ret.sto)
              | else =>
                raise("appE: " + fun-e + " cannot be evaluated to a function value")
            end
        end
    end
  end
  ##
  # interp-full-stmt:
  #
  #   Interpret one specific type of statement at once.
  #   For assign/defvar cases, it would lift the local variable to 
  #   "outter" scope if necessary (identifier not exists in
  #   the environment it can see).
  #
  fun interp-full-stmt(is-stmt :: Stmt, is-env :: Env, is-store :: Store):
    fun is-exists(e-is-id :: String, e-is-env :: Env, e-is-store) -> Bool:
      cases (Env) e-is-env:
        | mt-env => false
        | an-env(fn, loc, nxt-env) =>
          if fn == e-is-id:
            if not (fetch(loc, e-is-store) == nullV):
              true
            else:
              false
            end
          else:
            is-exists(e-is-id, nxt-env, e-is-store)
          end
      end
    end
    cases (Stmt) is-stmt:
      | expr-stmt(e) =>
        {
          res: interp-full-expr(e, is-env, is-store),
          env: is-env
        }
      | assign(id, e) =>
        id-loc = gensym("loc:")
        if is-exists(id, is-env, is-store):
          exp-ret = interp-full-expr(e, is-env, is-store)
          exp-val = exp-ret.val
          exp-sto = exp-ret.store
          {
            res: result(exp-val, a-store(id-loc, exp-val, exp-sto)),
            env: an-env(id, id-loc, is-env)
          }
        else:
          {
            res: result(nullV, a-store(id-loc, nullV, is-store)),
            env: an-env(id, id-loc, is-env)
          }
        end
      | defvar(id, e) =>
        id-loc = gensym("loc:")
        exp-ret = interp-full-expr(e, is-env, is-store)
        exp-val = exp-ret.val
        exp-sto = exp-ret.store
        {
          res: result(exp-val, a-store(id-loc, exp-val, exp-sto)),
          env: an-env(id, id-loc, is-env)
        }
      | else =>
        raise("unknown statement: " + is-stmt)
    end
  end
  ##
  # interp-full-stmts:
  # 
  #   Dispatch the interpreting work to interp-full in 
  #   recursive manner. In obeying to the rule of the parser
  #   where no empty block is allowed, the list passed in
  #   should never be empty.
  #
  fun interp-full-stmts(
        is-stmt-l :: List<Stmt>,
        is-env :: Env,
        is-store :: Store) -> Result:
    fun check-unbound(c-is-env :: Env, c-is-store :: Store, bound-ids :: Set<String>):
      cases (Env) c-is-env:
        | mt-env => nothing
        | an-env(fn, loc, nxt-env) =>
          if (not bound-ids.member(fn)) and (fetch(loc, c-is-store) == nullV):
            raise("Referencing unbound identifier: " + fn)
          else:
            check-unbound(nxt-env, c-is-store, bound-ids.add(fn))
          end
      end
    end
    cases (List<Stmt>) is-stmt-l:
      | link(stmt, nxt-stmts-l) =>
        st-ret = interp-full-stmt(stmt, is-env, is-store)
        st-res = st-ret.res
        st-nen = st-ret.env
        if nxt-stmts-l == empty:
          check-unbound(st-nen, st-res.store, set([]))
          st-res
        else:
          interp-full-stmts(nxt-stmts-l, st-nen, st-res.store)
        end
      | else =>
        raise("Contract violation: the input should never be empty list")
    end
  end
  ##
  # Entrance of interp-full:
  #
  #   Interpret the program, aka the statements, sequentially by 
  #   calling interp-full-stmt. For interpreting for every statement,
  #   it will probe one more link to see if it needs to return the
  #   current interpretted result as the final result.
  #
  interp-full-stmts(prog.stmts, env, store)
where:
  #######################################################
  # TC-V: Values
  #
  eval('
    null
  ') is nullV
  eval('
    5
  ') is numV(5)
  eval('
    5 6
  ') is numV(6)
  eval('
    "My name is parat"
  ') is strV("My name is parat")
  eval('
    (fun () 3)
  ').params.length() is 0
  eval('
    (fun () 3)
  ').env is mt-env
  eval('
    (fun () 3)
  ').body is block([expr-stmt(numE(3))])
  eval('
    (fun () 3 4)
  ').body is block([expr-stmt(numE(3)), expr-stmt(numE(4))])
  eval('
    (fun () (3))
  ').env is mt-env
  eval('
    (record (x 1))
  ') is recV([fieldV("x", numV(1))])
  eval('
    (record (x 1) (y 2))
  ') is recV([fieldV("x", numV(1)), fieldV("y", numV(2))])
  #######################################################
  # TC-BO: Binary Operation
  #
  eval('
    (+ "hello " "world")
  ') raises ""
  eval('
    (+ 3 "world")
  ') raises ""
  eval('
    (+ "Hello" 9)
  ') raises ""
  eval('
    (+ 3 (fun (x y) (+ x y)))
  ') raises ""
  eval('
    (+ (fun (x y) (+ x y)) 3)
  ') raises ""
  eval('
    (- "hello " "world")
  ') raises ""
  eval('
    (- 3 "world")
  ') raises ""
  eval('
    (- "Hello" 9)
  ') raises ""
  eval('
    (- 3 (fun (x y) (+ x y)))
  ') raises ""
  eval('
    (- (fun (x y) (+ x y)) 3)
  ') raises ""
  eval('
    (++ "hello " 8)
  ') raises ""
  eval('
    (++ 8 "hello")
  ') raises ""
  eval('
    (++ 6 9)
  ') raises ""
  eval('
    (++ "hello" (fun (x y) (+ x y)))
  ') raises ""
  eval('
    (++ (fun (x y) (+ x y)) "hello")
  ') raises ""
  eval('
    (== "hello" 1)
  ') raises ""
  eval('
    (== 1 "hello")
  ') raises ""
  eval('
    (== "hello" (fun (x y) (+ x y)))
  ') raises ""
  eval('
    (== (fun (x y) (+ x y)) "hello")
  ') raises ""
  eval('
    (+ 3 3)
  ') is numV(6)
  eval('
    (- 3 3)
  ') is numV(0)
  eval('
    (++ "hello " "world")
  ') is strV("hello world")
  eval('
    (== "hello" "hello")
  ') is numV(1)
  eval('
    (== "hello" "bybye")
  ') is numV(0)
  eval('
    (fun (x y) (+ x y))
  ').params.length() is 2
  eval('
    (fun (x y) (+ x y))
  ').body is block([expr-stmt(bopE(plus, idE("x"), idE("y")))])
  eval('
    (fun (x y)
         (+ x y))
  ').env is mt-env
  eval('
    (fun (x y)
         (+ x (+ y z)))
  ').params.length() is 2
  eval('
    (fun (x y)
         (+ x (+ y z)))
  ').body is block([expr-stmt(bopE(plus, idE("x"), bopE(plus, idE("y"), idE("z"))))])
  eval('
    (fun (x y)
         (+ x (+ y z)))
  ').env is mt-env
  #######################################################
  # TC-IF: If-else Expression
  #
  eval('
    (if 1 1 0)
  ') is numV(1)
  eval('
    (if 0 1 0)
  ') is numV(0)
  eval('
    (fun (x y)
         "doc"
         (if (== x y) 1 0))
  ') is 
    funV(
      ["x", "y"],
      block([expr-stmt(strE("doc")),
             expr-stmt(cifE(bopE(str-eq, idE("x"), idE("y")),
                            numE(1),
                            numE(0)))]),
      mt-env)
  eval('
    (fun (input)
         (if (== input "string-type")
             (fun (m n)
                  (if (== m n) "equal-value" "unequal-value"))
             (fun (m n)
                  (if (== m n) 1 0))))
  ') is 
    funV(
      ["input"],
      block([
        expr-stmt(
          cifE(
            bopE(str-eq, idE("input"), strE("string-type")),
            lamE(["m", "n"],
                 block([expr-stmt(
                   cifE(bopE(str-eq, idE("m"), idE("n")),
                        strE("equal-value"),
                        strE("unequal-value")))])),
            lamE(["m", "n"],
                 block([expr-stmt(
                   cifE(bopE(str-eq, idE("m"), idE("n")),
                        numE(1),
                        numE(0)))]))))]),
      mt-env)
  #######################################################
  # TC-RO: Record Operataion
  #
  eval('
    (lookup (record (x 1) (y 3)) x)
  ') is numV(1)
  eval('
    (lookup (extend (record (x 1) (y 3)) z 9) z)
  ') is numV(9)
  #######################################################
  # TC-AD: Assign and Defvar Statments
  #
  eval('
    (assign x 3)
  ') raises ""
  eval('
    (assign x 3)
    (defvar x 4)
  ') is numV(4)
  eval('
    (defvar y (fun () x))
    (defvar x 1)
  ') is numV(1)
  eval('
    (defvar y (fun () x))
    (defvar x 1)
    (y)
  ') is numV(1)
end
