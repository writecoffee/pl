#lang pyret/whalesong

data Expr:
  | idE(name :: String)
  | numE(value :: Number)
  | strE(value :: String)
  | uopE(op :: UnaryOperator, arg :: Expr)
  | bopE(op :: Operator, left :: Expr, right :: Expr)
  | cifE(cond :: Expr, consq :: Expr, altern :: Expr)
  | letE(name :: String, expr :: Expr, body :: Expr)
  | lamE(param :: String, body :: Expr)
  | appE(func :: Expr, arg :: Expr)
  | emptyE
end

data UnaryOperator:
  | firstOp
  | restOp
  | emptyOp # tests whether a list is empty
end

data Operator:
  | plus
  | minus
  | append
  | str-eq
  | linkOp
end

data Type:
  | varT(name :: String)
  | baseT(type :: BaseType)
  | conT(constr :: ConstrType, args :: List<Type>)
end

fun normalize(typ :: Type) -> Type:
  doc: "Put a type into a normal form, in which type variables are named sequentially."
  alphabet = "abcdefghijklmnopqrstuvwxyz"
  fun int-to-letter(n :: Number) -> String:
    if n < 26:
      alphabet.char-at(n)
    else:
      int-to-letter((n / 26).truncate() - 1) + alphabet.char-at(n.modulo(26))
    end
  end
  var mapping = [] # Map old variable names to new variable names
  var count = 0    # Keep track of the latest new variable name
  fun lookup-var(v :: String) -> String:
    cases(Option) mapping.find(fun(pair): pair.get(0) == v;):
      | some(pair) => pair.get(1)
      | none => v2 = int-to-letter(count)
                count := count + 1
                mapping := mapping + [[v, v2]]
                v2
    end
  end
  fun normalize-rec(t :: Type) -> Type:
    cases(Type) t:
      | varT(v) => varT(lookup-var(v))
      | baseT(b) => baseT(b)
      | conT(c, args) => conT(c, map(normalize-rec, args))
    end
  end
  normalize-rec(typ)
end

fun same-type(t1 :: Type, t2 :: Type) -> Bool:
  doc: "Check to see if two types are the same, up to variable renaming."
  normalize(t1) == normalize(t2)
end

data BaseType:
  | numT
  | strT
end

data ConstrType:
  | funT
  | listT
end

fun parse(prog) -> Expr:
  fun convert(sexpr):
    if sexpr == "empty":
      emptyE
    else if List(sexpr):
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
      else if head == "fun":
        when sexpr.get(1).length() <> 1:
          raise("In Polly, functions always take exactly one argument.")
        end
        lamE(sexpr.get(1).get(0), convert(sexpr.get(2)))
      else if head == "+":
        bopE(plus, convert(sexpr.get(1)), convert(sexpr.get(2)))
      else if head == "-":
        bopE(minus, convert(sexpr.get(1)), convert(sexpr.get(2)))
      else if head == "++":
        bopE(append, convert(sexpr.get(1)), convert(sexpr.get(2)))
      else if head == "==":
        bopE(str-eq, convert(sexpr.get(1)), convert(sexpr.get(2)))
      else if head == "link":
        bopE(linkOp, convert(sexpr.get(1)), convert(sexpr.get(2)))
      else if head == "first":
        uopE(firstOp, convert(sexpr.get(1)))
      else if head == "rest":
        uopE(restOp, convert(sexpr.get(1)))
      else if head == "empty?":
        uopE(emptyOp, convert(sexpr.get(1)))
      else:
        func = convert(head)
        arg = convert(sexpr.get(1))
        appE(func, arg)
      end
    else if Number(sexpr):
      numE(sexpr)
    else if String(sexpr):
      idE(sexpr)
    end
  end
  convert(prog)
end

data Constraint:
  | eqCon(lhs :: Type, rhs :: Type)
end

data Substitution:
  | sub(v :: Expr, w :: Type)
end

##
# 
# 
#
fun generate-constraints(exp :: Expr) -> List<Constraint>:
  empty
where:

end

##
#
#
#
fun unify(c-list :: List<Constraint>) -> List<Substitution>:
  nothing
where:

end

##
#
#
#
fun type-infer(prog :: String) -> Type:

where:
  
end
