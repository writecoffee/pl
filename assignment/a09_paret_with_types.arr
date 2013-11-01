#lang pyret/whalesong

data Type:
  | numT
  | strT
  | funT(params :: List<Type>, result :: Type)
  | recordT(fields :: List<FieldType>)
end

data FieldType:
  | fieldT(name :: String, type :: Type)
end

data TypeEnv:
  | mt-tenv
  | a-tenv(name :: String, type :: Type, tenv :: TypeEnv)
end

data Expr:
  | idE(name :: String)
  | numE(value :: Number)
  | strE(value :: String)
  | bopE(op :: Operator, left :: Expr, right :: Expr)
  | cifE(cond :: Expr, consq :: Expr, altern :: Expr)
  | letE(bind :: Binding, expr :: Expr, body :: Expr)
  | lamE(params :: List<Binding>, body :: Expr)
  | appE(func :: Expr, args :: List<Expr>)
  | assignE(name :: String, expr :: Expr)
  | doE(exprs :: List<Expr>)

  | recordE(fields :: List<Field>)
  | lookupE(rec :: Expr, field-name :: String)
  | extendE(rec :: Expr, field-name :: String, new-value :: Expr)
end

data Binding:
  | binding(name :: String, type :: Type)
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
  fun convert-binding(sexpr):
    when sexpr.get(1) <> ":":
      raise("parse - invalid binding: " + sexpr.tostring())
    end
        binding(sexpr.get(0), convert-type(sexpr.get(2)))
  end
  fun convert-type(sexpr):
    if sexpr == "num":
      numT
    else if sexpr == "str":
      strT
    else if sexpr.get(0) == "record":
      recordT(map(convert-field-type, sexpr.rest))
    else if sexpr.get(sexpr.length() - 2) == "->":
      funT(map(convert-type, sexpr.take(sexpr.length() - 2)),
                   convert-type(sexpr.last()))
    end
  end
  fun convert-field-type(sexpr):
        fieldT(sexpr.get(0), convert-type(sexpr.get(1)))
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
        letE(convert-binding(sexpr.get(1).get(0)),
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
        lamE(map(convert-binding, sexpr.get(1)), convert(sexpr.get(2)))
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

fun type-of(prog :: String) -> Type:
  type-of-full(parse(read-sexpr(prog)), mt-tenv)
end

fun type-of-full(prog :: Expr, tenv :: TypeEnv) -> Type:
  fun is-str-type(type) -> Bool:
    if type == strT:
      true
    else:
      false
    end
  end
  fun is-num-type(type) -> Bool:
    if type == numT:
      true
    else:
      false
    end
  end
  fun type-of-operation(op :: Operator, lt :: Type, rt :: Type) -> Type:
    fun get-type(is-what-type):
      if not (is-what-type(lt) and is-what-type(rt)):
        raise("illegal operands for binary operation")
      else:
        lt
      end
    end
    cases (Operator) op:
      | plus =>
        get-type(is-num-type)
      | minus =>
        get-type(is-num-type)
      | append =>
        get-type(is-str-type)
      | str-eq =>
        get-type(is-str-type)
    end
  end
  fun type-of-fields(f-l :: List<Field>, f-tenv :: TypeEnv) -> List<FieldType>:
    cases (List<Field>) f-l:
      | empty =>
        empty
      | link(f, f-nxt) =>
        ft = type-of-full(f.value, f-tenv)
        link(fieldT(f.name, ft), type-of-fields(f-nxt, f-tenv))
    end
  end
  fun concat-tenv(tenv1 :: TypeEnv, tenv2 :: TypeEnv) -> TypeEnv:
    cases (TypeEnv) tenv1:
      | mt-tenv =>
        tenv2
      | a-tenv(e1-n, e1-t, e1-ext) =>
        a-tenv(e1-n, e1-t, concat-tenv(e1-ext, tenv2))
    end
  end
  fun type-of-parameters(p-l :: List<Binding>):
    var lam-env :: TypeEnv = mt-tenv
    fun retrieve-p-l-types(r-p-l :: List<Binding>) -> List<Type>:
      cases (List<Binding>) r-p-l:
        | empty =>
          empty
        | link(pb, pb-nxt) =>
          pbn = pb.name
          pbt = pb.type
          lam-env := a-tenv(pbn, pbt, lam-env)
          link(pbt, retrieve-p-l-types(pb-nxt))
      end
    end
    {
      tps : retrieve-p-l-types(p-l),
      env : lam-env
    }
  end
  fun lookup-tenv(id-n :: String, id-tenv :: TypeEnv) -> Type:
    cases (TypeEnv) id-tenv:
      | mt-tenv =>
        raise("unbound id: " +  id-n)
      | a-tenv(n, t, nxt-tenv) =>
        if n == id-n:
          t
        else:
          lookup-tenv(id-n, nxt-tenv)
        end
    end
  end
  fun type-of-arguments(a-l :: List<Expr>, a-l-tenv :: TypeEnv)
      -> List<Type>:
    cases (List<Expr>) a-l:
      | empty =>
        empty
      | link(e, nxt-e) =>
        et = type-of-full(e, a-l-tenv)
        link(et, type-of-arguments(nxt-e, a-l-tenv))
    end
  end
  ##
  # Helper Function: is-type-match
  #
  #   This routine is used for checking two types are exactly the same.
  #   For funT case, it requires all paramter pairs are of the same type.
  #   The same rule applies to their result type; for recordT case, it
  #   requires the second recordE's fieldE list contains the one of
  #   the first recordE.
  #
  fun is-type-match(t1 :: Type, t2 :: Type) -> Bool:
    fun make-type-pairs(p1-l :: List<Type>, p2-l :: List<Type>):
      cases (List<Type>) p1-l:
        | empty => empty
        | link(t, nxt-t) =>
          link({t1 : t, t2 : p2-l.first},
               make-type-pairs(nxt-t, p2-l.rest))
      end 
    end
    fun is-record-contains-field(f :: FieldType, f-l :: List<Field>) -> Bool:
      cases (List<Field>) f-l:
        | empty => false
        | link(tf, nxt-tf) =>
          if (tf.name == f.name):
            if is-type-match(tf.type, f.type):
              true
            else:
              false
            end
          else:
            is-record-contains-field(f, nxt-tf)
          end
      end
    end
    cases (Type) t1:
      | numT =>
        t1 == t2
      | strT =>
        t1 == t2
      | recordT(ft-l) =>
        cases (Type) t2:
          | recordT(_) =>
            if ft-l.length() > t2.fields.length():
              false
            else:
              for fold(res from true, pft from ft-l):
                res and is-record-contains-field(pft, t2.fields)
              end
            end
          | else =>
            false
        end
      | funT(pt-l, r) =>
        cases (Type) t2:
          | funT(_) =>
            t-pairs = make-type-pairs(pt-l.append([r]),
                                      t2.params.append([t2.result]))
            for fold(res from true, tp from t-pairs):
              res and is-type-match(tp.t1, tp.t2)
            end
          | else =>
            false
        end
    end
  end
  fun perform-argument-check(p-l :: List<Type>, a-l :: List<Type>):
    if not (p-l.length() == a-l.length()):
      raise("arity mismatch for function application")
    else:
      fun arg-check(c-p-l :: List<Type>, c-a-l :: List<Type>):
        cases (List<Type>) c-p-l:
          | empty => 
            nothing
          | link(t, nxt-t) =>
            if is-type-match(t, c-a-l.first):
              arg-check(nxt-t, c-a-l.rest)
            else:
              raise("type mismatch between argument and " +
                    "parameter when applying function")
            end
        end
      end
      arg-check(p-l, a-l)
    end
  end
  cases (Expr) prog:
    | numE(n) =>
      numT
    | strE(s) =>
      strT
    | bopE(op, left, right) =>
      lt-ret = type-of-full(left, tenv)
      rt-ret = type-of-full(right, tenv)
      type-of-operation(op, lt-ret, rt-ret)
    | recordE(f-l) =>
      recordT(type-of-fields(f-l, tenv))
    | lamE(p-l, body) =>
      pt-ret = type-of-parameters(p-l)
      pt-env = pt-ret.env
      pt-tps = pt-ret.tps
      funT(pt-tps, type-of-full(body, concat-tenv(pt-env, tenv)))
    | idE(n) =>
      lookup-tenv(n, tenv)
    | appE(fun-e, arg-l) =>
      cases (Expr) fun-e:
        | lamE(_, _) =>
          fun-t = type-of-full(fun-e, tenv)
          arg-t-l = type-of-arguments(arg-l, tenv)
          perform-argument-check(fun-t.params, arg-t-l)
          fun-t.result
# TODO: add test cases combined with let
        | else =>
          oe-t = type-of-full(fun-e, tenv)
          cases (Type) oe-t:
            | funT(_, _) =>
              oe-t
            | else =>
              raise("cannot apply on non-func type")
          end
      end
    | else =>
      raise("unrecognizable expression")
  end
where:
  fun check-basic-value-types():
    type-of('2')
      is numT
    type-of('"I am a string"')
      is strT
    type-of('(+ 2 3)')
      is numT
    type-of('(- 2 3)')
      is numT
    type-of('(== "str1" "str2")')
      is strT
    type-of('(++ "str1" "str2")')
      is strT
    type-of('(+ 2 "hI")')
      raises "illegal operands for binary operation"
    type-of('(+ "not-a-num" 2)')
      raises "illegal operands for binary operation"
    type-of('(== "not-a-num" 2)')
      raises "illegal operands for binary operation"
    type-of('(== 2 "not-a-num")')
      raises "illegal operands for binary operation"
    type-of('(++ "not-a-num" 2)')
      raises "illegal operands for binary operation"
    type-of('(++ 2 "not-a-num")')
      raises "illegal operands for binary operation"
  end
  fun check-record-value-types():
    type-of('
      (record (x 10) (y "hello"))
    ') is recordT([fieldT("x", numT), fieldT("y", strT)])
    type-of('
      ((fun ((record-parm : (record (x num))))
           "result-string")
      (record (x 99)))
    ') is strT
    type-of('
      ((fun ((record-parm : (record (x num))))
           "result-string")
      (record (x "mismatch string")))
    ') raises "type mismatch between argument and " +
              "parameter when applying function"
    type-of('
      ((fun ((record-parm : (record (x num) (y num))))
           "result-string")
      (record (x 9)))
    ') raises "type mismatch between argument and " +
              "parameter when applying function"
    type-of('
      ((fun ((record-parm : (record (x num) (y num))))
           "result-string")
      (record (y 9) (x 77) (z "extra-string")))
    ') is strT
  end
  fun check-fun-value-types():
    type-of('
      (fun ((x : num)) 3)
    ') is funT([numT], numT)
    type-of('
      (fun ((x : num)) x)
    ') is funT([numT], numT)
    type-of('
      (fun ((x : num) (y : str))
           x)
    ') is funT([numT, strT], numT)
    type-of('
      (fun ((x : (record (a num))))
           x)
    ') is funT([recordT([fieldT("a", numT)])],
               recordT([fieldT("a", numT)]))
    type-of('
      (fun ((fun-parm : num -> num))
           fun-parm)
    ') is funT([numT], numT)
    type-of('
      (fun ((fun-parm : (str num -> num)))
           fun-parm)
    ') is funT([funT([strT, numT], numT)],
               funT([strT, numT], numT))
  end
  fun check-application-types():
    type-of('
      ((fun ((x : num)) 3) 9)
    ') is numT
    type-of('
      ((fun ((x : num) (y : num)) 3) 9 99)
    ') is numT
    type-of('
      ((fun ((x : num)) 3) 9 77)
    ') raises "arity mismatch for function application"
    type-of('
      ((fun ((x : num) (y : num)) 3) 9)
    ') raises "arity mismatch for function application"
    type-of('
      ((fun ((x : num)) 3) "a-psydo-umber")
    ') raises "type mismatch between argument and " +
              "parameter when applying function"
    type-of('
      ((fun ((x : str)) "string-result") 77)
    ') raises "type mismatch between argument and " +
              "parameter when applying function"
  end
  check-basic-value-types()
  check-record-value-types()
  check-fun-value-types()
  check-application-types()
end
