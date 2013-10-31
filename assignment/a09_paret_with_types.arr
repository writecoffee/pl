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
  cases (Expr) prog:
    | numE(n) =>
      numT
    | strE(s) =>
      strT
    | bopE(op, left, right) =>
      lt-ret = type-of-full(left, tenv)
      rt-ret = type-of-full(right, tenv)
      type-of-operation(op, lt-ret, rt-ret)
  end
where:
  type-of('2') is numT
  type-of('"I am a string"') is strT
  type-of('(+ 2 3)') is numT
  type-of('(- 2 3)') is numT
  type-of('(== "str1" "str2")') is strT
  type-of('(++ "str1" "str2")') is strT
  type-of('(+ 2 "hI")') raises "illegal operands for binary operation"
  type-of('(+ "not-a-num" 2)') raises "illegal operands for binary operation"
  type-of('(== "not-a-num" 2)') raises "illegal operands for binary operation"
  type-of('(== 2 "not-a-num")') raises "illegal operands for binary operation"
  type-of('(++ "not-a-num" 2)') raises "illegal operands for binary operation"
  type-of('(++ 2 "not-a-num")') raises "illegal operands for binary operation"
end
