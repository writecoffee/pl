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

data BaseType:
  | numT
  | strT
end

data ConstrType:
  | funT
  | listT
end

DEBUG = true
NODEBUG = false

GEN_VAR_ID = fun() -> String:
  if DEBUG:
    ""
  else:
    gensym("varT-")
  end
end

data Term:
  | tLink(value :: Expr, next :: Expr, mutable etypes :: List<Type>) with:
    add-matched(self, et :: Type) -> List<Type>:
      self!{etypes : self!etypes + [et]}
    end
  | tType(type :: Type)
  | tExpr(expr :: Expr)
end

data EqualCondition:
  | eqCon(lhs :: Term, rhs :: Term)
end

data Substitution:
  | substitution(mutable econs :: List<EqualCondition>) with:
    replace(self, in :: Expr, with :: Type) -> List<EqualCondition>:
      fun replace-helper(i :: Number, old-econs :: List<EqualCondition>) -> Bool:
        cases (List<EqualCondition>) old-econs:
          | empty =>
            false
          | link(econ, rest) =>
            cases (Term) econ.rhs:
              | tLink(value, next, etypes) =>
                if (value == in) and (etypes == empty):
                  oe = self!econs.get(i)
                  ne = oe!{etypes : oe!etypes + [with]}
                  self!{econs : self!econs.set(i, ne)}
                else if (next == in) and (etypes.length() == 1):
                  oe = self!econs.get(i)
                  ne = oe!{etypes : oe!etypes + [with]}
                  self!{econs : self!econs.set(i, ne)}
# TODO: plug itself to its upstream
                else:
                  replace-helper(i + 1, rest)
                end
            end
        end
      end
      if replace-helper(1, self!econs.rest):
        self!{econs : self!econs.rest}
      else:
      end
    end
end

data Constraint:
  | constraint(c-list :: List<EqualCondition>)
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

##
# GEN_CONSTR: 
#     Constraint generation. It walks the program source, emitting
#     appropriate constraints on each expression, and returns this
#     SET of constraints, aka, the returned list should be
#     interpreted as a set.
#
fun GEN_CONSTR(exp :: Expr) -> List<EqualCondition>:
  cases (Expr) exp:
    | numE(n) =>
      [eqCon(tExpr(exp), tType(baseT(numT)))]
    | strE(s) =>
      [eqCon(tExpr(exp), tType(baseT(strT)))]
    | idE(s) =>
      [eqCon(tExpr(exp), tType(varT(GEN_VAR_ID())))]
    | emptyE =>
      [eqCon(tExpr(emptyE), tType(conT(listT, [varT(GEN_VAR_ID())])))]
    | bopE(op, l, r) =>
      cases (Operator) op:
        | linkOp =>
          GEN_CONSTR(r) + GEN_CONSTR(l) + [eqCon(tExpr(exp), tLink(l, r, []))]
      end
    | else =>
      raise("Other expression cases are not-yet-considered for " +
            "constraints generation")
  end
where:
  TEST_GEN_CONSTR = fun(exp :: String) -> List<EqualCondition>:
    GEN_CONSTR(parse(read-sexpr(exp)))
  end
  nothing
end

##
# UNIFY:
#     The goal of unification is to generate a substitution, or
#     mapping from variables to terms that do not contain any
#     variables. For a given constraint, the unifier examines the
#     left-hand-side of the equation. It it is a variable, it is
#     now ripe for elimination. The unifier adds the variable's
#     right-hand-side to the substitution and, to truly eliminate
#     it, replaces all occurrences of the variable in the
#     substitution with this right-hand-side.
#
fun UNIFY(constr :: Constraint, substr :: Substitution) -> Substitution:
  cases (List<EqualCondition>) constr.c-list:
    | empty =>
      substr
    | link(c, rest) =>
      l = c.lhs.expr
      r = c.rhs
      substr!{econs : [c] + substr!econs}
      cases (Term) r:
        | tType(type) =>
          substr.replace(l, type)
          UNIFY(constraint(rest), substr)
        | else =>
          UNIFY(constraint(rest), substr)
      end
  end
where:

end

##
# type-infer:
#     It traverses the substitution and find the types of all
#     the expression in the program and then insert the type
#     annotations accordingly.
#
fun type-infer(prog :: String) -> Type:
  prog-exp = parse(read-sexpr(prog))
  cons-lst = GEN_CONSTR(prog-exp)
  subst = UNIFY(constraint(cons-lst), substitution([]))
  subst!econs.get(0).rhs.type
where:
  TEST_INFER_PASS = fun (prog :: String, expected :: Type, debug :: Bool):
    if debug:
      print("============= testing =============")
      print(prog)
      print("------------ expecting ------------")
      print(expected)
    else:
      nothing
    end
    type-infer(prog) satisfies same-type(_, expected)
  end
  TEST_INFER_PASS('
    3
  ', baseT(numT), DEBUG)
  TEST_INFER_PASS('
    empty
  ', conT(listT, [varT("varT-")]), DEBUG)

#  type-infer('
#    (fun (x) x)
#  ') satisfies same-type(_, conT(funT, [varT("q"), varT("p")]))

end
