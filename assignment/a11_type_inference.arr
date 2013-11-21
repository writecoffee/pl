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

DEBUG = false
NODEBUG = false
DELIBERATE_ID = true

GEN_VAR_ID = fun() -> String:
  if DELIBERATE_ID:
    ""
  else:
    gensym("varT-")
  end
end

fun IS_TYPE_VAR(type :: Type) -> Bool:
  cases (Type) type:
    | varT(_) => true
    | else => false
  end
end

fun IS_TYPE_LINK(type :: Type) -> Bool:
  cases (Type) type:
    | conT(constr, _) =>
      (constr == listT)
    | else =>
      false
  end
end

data Term:
  | tUopr(arg-first :: Expr,
          arg-rest :: Expr,
          mutable etypes :: List<Type>) with:
    add-matched(self, in :: Expr, with :: Type) -> Bool:
      if (self.arg-first == in) and (self!etypes == empty):
        self!{etypes : self!etypes + [with]}
        true
      else if (self.arg-rest == in) and (self!etypes.length() == 1)
                                    and (IS_TYPE_LINK(with) or IS_TYPE_VAR(with)):
# TODO: test (fun (param) (rest param)),
#       return "conT(listT, [varT("q")])" or "conT(listT, [varT("p"), varT("q")])"
        self!{etypes : self!etypes + [with]}
        true
      else:
        false
      end
    end,
    is-unified(self) -> Bool:
      (self!etypes.length() == 2)
    end,
    get-expected-type(self) -> Type:
      self!etypes.get(1)
    end,
    get-constraint-type(self) -> Option:
      none
    end
  | tUopf(arg-first :: Expr,
          arg-rest :: Expr,
          mutable etypes :: List<Type>) with:
    add-matched(self, in :: Expr, with :: Type) -> Bool:
      if (self.arg-first == in) and (self!etypes == empty):
        self!{etypes : self!etypes + [with]}
        true
      else if (self.arg-rest == in) and (self!etypes.length() == 1)
                                    and (IS_TYPE_LINK(with) or IS_TYPE_VAR(with)):
# TODO: test (fun (param) (first param))
        self!{etypes : self!etypes + [with]}
        true
      else:
        false
      end
    end,
    is-unified(self) -> Bool:
      (self!etypes.length() == 2)
    end,
    get-expected-type(self) -> Type:
      self!etypes.get(0)
    end,
    get-constraint-type(self) -> Option:
      none
    end
  | tUope(arg :: Expr,
          mutable etypes :: List<Type>) with:
    add-matched(self, in :: Expr, with :: Type) -> Bool:
      if (self.arg == in) and (self!etypes == empty)
                          and (IS_TYPE_LINK(with) or IS_TYPE_VAR(with)):
# TODO: test (fun (param) (empty param))
        self!{etypes : self!etypes + [with]}
        true
      else:
        false
      end
    end,
    is-unified(self) -> Bool:
      (self!etypes.length() == 1)
    end,
    get-expected-type(self) -> Type:
      baseT(numT)
    end,
    get-constraint-type(self) -> Option:
      baseT(numT)
    end
  | tCifs(cond-exp :: Expr,
          seq-exp :: Expr,
          alt-exp :: Expr,
          mutable etypes :: List<Type>) with:
    add-matched(self, in :: Expr, with :: Type) -> Bool:
      var result = true
      if (self.cond-exp == in) and (self!etypes == empty):
        self!{etypes : self!etypes + [with]}
      else if (self.seq-exp == in) and (self!etypes.length() == 1):
        self!{etypes : self!etypes + [with]}
      else if (self.alt-exp == in) and (self!etypes.length() == 2):
        if (self!etypes.get(1) == with):
          self!{etypes : self!etypes + [with]}
        else if (IS_TYPE_VAR(self!etypes.get(1))):
          self!{etypes : [self!etypes.first] + [with, with]}
        else:
          result := false
        end
      else:
        result := false
      end
      result
    end,
    is-unified(self) -> Bool:
      (self!etypes.length() == 3)
    end,
    get-expected-type(self) -> Type:
      self!etypes.get(1)
    end,
    get-constraint-type(self) -> Option:
      if (self!etypes.length() > 1) and (not IS_TYPE_VAR(self!etypes.get(1))):
        self!etypes.get(1)
      else:
        none
      end
    end
  | tBind(bind-exp :: Expr,
          mutable etypes :: List<Type>) with:
    add-matched(self, in :: Expr, with :: Type) -> Bool:
      if (self.bind-exp == in) and (self!etypes == empty):
        self!{etypes : self!etypes + [with]}
        true
      else:
        false
      end
    end,
    is-unified(self) -> Bool:
      (self!etypes.length() == 1)
    end,
    get-expected-type(self) -> Type:
      self!etypes.get(0)
    end,
    get-constraint-type(self) -> Option:
      none
    end
  | tLbdy(bind-id :: Expr,
          body :: Expr,
          mutable etypes :: List<Type>) with:
    add-matched(self, in :: Expr, with :: Type) -> Bool:
      if (self.bind-id == in) and (self!etypes == empty):
        self!{etypes : self!etypes + [with]}
        true
      else if (self.body == in) and (self!etypes.length() == 1):
        self!{etypes : self!etypes + [with]}
        true
      else:
        false
      end
    end,
    is-unified(self) -> Bool:
      (self!etypes.length() == 2)
    end,
    get-expected-type(self) -> Type:
      self!etypes.get(1)
    end,
    get-constraint-type(self) -> Option:
      none
    end
  | tBbop(type :: Type,
          bop :: Operator,
          left :: Expr,
          right :: Expr,
          mutable etypes :: List<Type>) with:
    add-matched(self, in :: Expr, with :: Type) -> Bool:
      if (self.left == in) and ((self.type == with) or IS_TYPE_VAR(with))
                           and (self!etypes == empty):
        self!{etypes : self!etypes + [self.type]}
        true
      else if (self.right == in) and ((self.type == with) or IS_TYPE_VAR(with))
                                 and (self!etypes.length() == 1):
        self!{etypes : self!etypes + [self.type]}
        true
      else:
        false
      end
    end,
    is-unified(self) -> Bool:
      (self!etypes.length() == 2) and
      (self!etypes.get(0) == self.type) and
      (self!etypes.get(1) == self.type)
    end,
    get-expected-type(self) -> Type:
      self.type
    end,
    get-constraint-type(self) -> Option:
      self.type
    end
  | tFunc(param :: Expr, body :: Expr, mutable etypes :: List<Type>) with:
    add-matched(self, in :: Expr, with :: Type) -> Bool:
      var result = false
      if (self.param == in):
        self!{etypes : [with] + self!etypes.rest}
        result := true
      else: nothing
      end
      if (self.body == in):
        self!{etypes : [self!etypes.first] + [with]}
        result := true
      else: nothing
      end
      result
    end,
    is-unified(self) -> Bool:
      self!etypes.length() == 2
    end,
    get-expected-type(self) -> Type:
      conT(funT, self!etypes)
    end,
    get-constraint-type(self) -> Option:
      none
    end
  | tLink(value :: Expr, next :: Expr, mutable etypes :: List<Type>) with:
    add-matched(self, in :: Expr, with :: Type) -> Bool:
      if (self.value == in) and (self!etypes == empty):
        self!{etypes : self!etypes + [with]}
        true
      else if (self.next == in) and (self!etypes.length() == 1):
        self!{etypes : self!etypes + [with]}
        true
      else:
        false
      end
    end,
    is-unified(self) -> Bool:
      self!etypes.length() == 2
    end,
    get-expected-type(self) -> Type:
      conT(listT, self!etypes)
    end,
    get-constraint-type(self) -> Option:
      none
    end
  | tType(type :: Type) with:
    get-expected-type(self) -> Type:
      self.type
    end,
    is-unified(self) -> Bool:
      true
    end
  | tExpr(expr :: Expr)
end

data EqualCondition:
  | eqCon(lhs :: Term, rhs :: Term)
end

data Substitution:
  | substitution(mutable econs :: List<EqualCondition>) with:
    replace-helper(self,
                   i :: Number,
                   in-e :: Expr,
                   with-e :: Type,
                   old-econs :: List<EqualCondition>) -> Bool:
      cases (List<EqualCondition>) old-econs:
        | empty =>
          false
        | link(econ, rest) =>
          if econ.rhs.add-matched(in-e, with-e):
            if IS_TYPE_VAR(with-e) and (econ.rhs.get-constraint-type() <> none):
              res-lookup :: Option = self.lookup-helper(in-e.name, rest)
              if res-lookup <> none:
                self.replace-helper(i + 1, in-e, econ.rhs.get-expected-type(), rest)
              else:
                raise("unbound identifier: " + in-e.name)
              end
            else:
            end
            if econ.rhs.is-unified():
              res-expr = econ.lhs.expr
              res-type = econ.rhs.get-expected-type()
              if self.replace-helper(i + 1, res-expr, res-type, rest):
#                  self!{econs : self!econs.drop(i)}
# TODO: drop the middle (i) here
                nothing
              else: nothing
              end
            else: nothing
            end
            true
          else:
            self.replace-helper(i + 1, in-e, with-e, rest)
          end
      end
    end,
    replace(self, in :: Expr, with :: Type) -> Bool:
      if (self!econs.length() == 1):
        true
      else if self.replace-helper(1, in, with, self!econs.rest):
        self!{econs : self!econs.rest}
        true
      else:
        false
      end
    end,
    lookup-helper(self,
                  id-lookup :: String,
                  old-econs :: List<EqualCondition>) -> Option:
      cases (List<EqualCondition>) old-econs:
        | empty => none
        | link(econ, rest) =>
          cases (Expr) econ.lhs.expr:
            | lamE(param, _) =>
              if (param == id-lookup) and (econ.rhs!etypes <> empty):
                some(econ.rhs!etypes.get(0))
              else:
                self.lookup-helper(id-lookup, rest)
              end
            | letE(name, _, _) =>
              if (name == id-lookup) and (econ.rhs!etypes <> empty):
                some(econ.rhs!etypes.get(0))
              else:
                self.lookup-helper(id-lookup, rest)
              end
            | appE(lambda, _) =>
              if (lambda.param == id-lookup) and (econ.rhs!etypes <> empty):
                some(econ.rhs!etypes.get(0))
              else:
                self.lookup-helper(id-lookup, rest)
              end
            | else =>
              self.lookup-helper(id-lookup, rest)
          end
      end
    end,
    lookup(self, id-lookup :: String) -> Option:
      self.lookup-helper(id-lookup, self!econs.rest)
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
          GEN_CONSTR(r) + GEN_CONSTR(l)
                        + [eqCon(tExpr(exp), tLink(l, r, []))]
        | plus =>
          GEN_CONSTR(r) + GEN_CONSTR(l)
                        + [eqCon(tExpr(exp), tBbop(baseT(numT), plus, l, r, []))]
        | minus =>
          GEN_CONSTR(r) + GEN_CONSTR(l)
                        + [eqCon(tExpr(exp), tBbop(baseT(numT), minus, l, r, []))]
        | append =>
          GEN_CONSTR(r) + GEN_CONSTR(l)
                        + [eqCon(tExpr(exp), tBbop(baseT(strT), append, l, r, []))]
        | str-eq =>
          GEN_CONSTR(r) + GEN_CONSTR(l)
                        + [eqCon(tExpr(exp), tBbop(baseT(strT), str-eq, l, r, []))]
      end
    | lamE(param, body) => 
      GEN_CONSTR(body) + GEN_CONSTR(idE(param))
                       + [eqCon(tExpr(exp), 
                                tFunc(idE(param),
                                      body,
                                      [varT(GEN_VAR_ID())]))]
    | letE(name, bind-exp, body) =>
      GEN_CONSTR(body) + GEN_CONSTR(bind-exp)
                       + [eqCon(tExpr(idE(name)), tBind(bind-exp, []))]
                       + [eqCon(tExpr(exp), tLbdy(idE(name), body, []))]
    | cifE(cond, seq, alt) =>
      GEN_CONSTR(alt) + GEN_CONSTR(seq)
                      + GEN_CONSTR(cond)
                      + [eqCon(tExpr(exp), tCifs(cond, seq, alt, []))]
    | appE(func, arg) =>
      cases (Expr) func:
        | lamE(param, body) =>
          GEN_CONSTR(body) + GEN_CONSTR(arg)
                           + [eqCon(tExpr(idE(param)), tBind(arg, []))]
                           + [eqCon(tExpr(exp), tLbdy(idE(param), body, []))]
# TODO: add id lambda
        | else =>
          raise("cannot apply a non-lambda expression")
      end
    | uopE(uop, arg) =>
      cases (UnaryOperator) uop:
        | emptyOp =>
# TODO: add id case
          GEN_CONSTR(arg) + [eqCon(tExpr(exp), tUope(arg, []))]
        | firstOp =>
# TODO: add id case
          cases (Expr) arg:
            | bopE(bop, first, rest) =>
              if (bop == linkOp):
                GEN_CONSTR(rest) + GEN_CONSTR(first)
                                  + [eqCon(tExpr(exp), tUopf(first, rest, []))]
              else:
                raise("firstOp: cannot apply on a non-link expression")
              end
            | else =>
              raise("firstOp: cannot apply on a non-link expression")
          end
        | restOp =>
# TODO: add id case
          cases (Expr) arg:
            | bopE(bop, first, rest) =>
              if (bop == linkOp):
                GEN_CONSTR(rest) + GEN_CONSTR(first)
                                  + [eqCon(tExpr(exp), tUopr(first, rest, []))]
              else:
                raise("restOp: cannot apply on a non-link expression")
              end
            | else =>
              raise("restOp: cannot apply on a non-link expression")
          end
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
          cases (Type) type:
            | varT(var-name) =>
              res-lookup :: Option = substr.lookup(l.name)
              if res-lookup <> none:
                if not substr.replace(l, res-lookup.value):
                  raise("unification error: " + l.name)
                else: nothing
                end
              else:
                raise("unbound identifier: " + l.name)
              end
              UNIFY(constraint(rest), substr)
            | else =>
              if not substr.replace(l, type):
                raise("unification error on baseT")
              else: nothing
              end
              UNIFY(constraint(rest), substr)
          end
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
  subst = UNIFY(constraint(cons-lst.reverse()), substitution([]))
  if not subst!econs.last().rhs.is-unified():
    raise("there must be bug in the program")
  else:
    subst!econs.last().rhs.get-expected-type()
  end
where:
  TEST_INFER_PASS = fun (prog :: String, expected :: Type, debug :: Bool):
    if debug:
      print("================ testing ================")
      print(prog)
      print("--------------- expecting ---------------")
      print(expected)
      type-infer(prog) satisfies same-type(_, expected)
      print("~~~~~~~~~~~~~~~~~ DONE ~~~~~~~~~~~~~~~~~~")
    else:
      type-infer(prog) satisfies same-type(_, expected)
    end
  end
  TEST_INFER_FAIL = fun (prog :: String, exception :: String, debug :: Bool):
    if debug:
      print("================ testing ================")
      print(prog)
      print("--------- expecting exception -----------")
      print(exception)
      type-infer(prog) raises exception
      print("~~~~~~~~~~~~~~~~~ DONE ~~~~~~~~~~~~~~~~~~")
    else:
      type-infer(prog) raises ""
    end
  end
  fun test-bop():
    TEST_INFER_FAIL('
      (+ unbound 3)
    ', "unbound identifier: unbound", DEBUG)
    TEST_INFER_FAIL('
      (+ "string-value" 3)
    ', "unification error on baseT", DEBUG)
  end
  fun test-link():
    TEST_INFER_PASS('
      3
    ', baseT(numT), DEBUG)
    TEST_INFER_PASS('
      "hello"
    ', baseT(strT), DEBUG)
    TEST_INFER_PASS('
      empty
    ', conT(listT, [varT("varT-")]), DEBUG)
    TEST_INFER_PASS('
      (link "hello" empty)
    ', conT(listT, [baseT(strT), conT(listT, [varT("varT-")])]), DEBUG)
    TEST_INFER_PASS('
      (link 3 (link "hello" empty))
    ', conT(listT,
            [baseT(numT),
             conT(listT,
                  [baseT(strT),
                   conT(listT,
                        [varT("varT-")])])]), DEBUG)
  end
  fun test-fun():
    TEST_INFER_FAIL('
      (fun (param) unbound)
    ', "unbound identifier: unbound", DEBUG)
    TEST_INFER_PASS('
      (fun (param) 3)
    ', conT(funT, [varT("varT-"), baseT(numT)]), DEBUG)
    TEST_INFER_PASS('
      (fun (param) param)
    ', conT(funT, [varT("varT-"), varT("varT-")]), DEBUG)
    TEST_INFER_PASS('
      (fun (param) (link 3 empty))
    ', conT(funT, [varT("varT-"),
                   conT(listT,
                        [baseT(numT),
                         conT(listT,
                              [varT("varT-")])])]), DEBUG)
    TEST_INFER_PASS('
      (fun (param) (+ 3 param))
    ', conT(funT, [baseT(numT), baseT(numT)]), DEBUG)
    TEST_INFER_FAIL('
      (fun (param) (+ 3 unbound))
    ', "unbound identifier: unbound", DEBUG)
  end
  fun test-let():
    TEST_INFER_PASS('
      (let (my-id 3) my-id)
    ', baseT(numT), DEBUG)
    TEST_INFER_FAIL('
      (let (my-id 3) unbound)
    ', "unbound identifier: unbound", DEBUG)
    TEST_INFER_FAIL('
      (let (my-id 3) 
           (let (my-shadow-id 99) unbound))
    ', "unbound identifier: unbound", DEBUG)
    TEST_INFER_PASS('
      (let (my-id 3) 
           (let (my-shadow-id 99) my-id))
    ', baseT(numT), DEBUG)
    TEST_INFER_PASS('
      (let (my-id (+ 77 3)) 
           (let (my-shadow-id 99) my-id))
    ', baseT(numT), DEBUG)
    TEST_INFER_PASS('
      (let (my-id 3)
           (let (my-shadow-id (+ 88 77)) my-id))
    ', baseT(numT), DEBUG)
    TEST_INFER_PASS('
      (let (my-id 3) 
           (let (my-shadow-id (+ my-id 77))
                my-id))
    ', baseT(numT), DEBUG)
    TEST_INFER_PASS('
      (let (my-id 3) 
           (let (my-id (+ my-id 77))
                my-id))
    ', baseT(numT), DEBUG)
    TEST_INFER_FAIL('
      (let (my-id my-id)
           3)
    ', "unbound identifier: my-id", DEBUG)
    TEST_INFER_FAIL('
      (let (my-id "str-value")
           (+ my-id 3))
    ', "unification error: my-id", DEBUG)
  end
  fun test-cif():
    TEST_INFER_PASS('
      (if 1 "true" "false")
    ', baseT(strT), DEBUG)
    TEST_INFER_FAIL('
      (if 1 999 "false")
    ', "unification error on baseT", DEBUG)
    TEST_INFER_PASS('
      (if "condition"
          999
          (+ 3 7))
    ', baseT(numT), DEBUG)
    TEST_INFER_PASS('
      (fun (param)
           (if "condition"
               999
               (+ 3 param)))
    ', conT(funT, [baseT(numT), baseT(numT)]), DEBUG)
    TEST_INFER_PASS('
      (fun (param)
           (if param
               999
               (+ 3 param)))
    ', conT(funT, [baseT(numT), baseT(numT)]), DEBUG)
    TEST_INFER_PASS('
      (fun (param)
           (if param
               param
               (+ 3 param)))
    ', conT(funT, [baseT(numT), baseT(numT)]), DEBUG)
    TEST_INFER_PASS('
      (fun (param)
           (if param
               param
               (+ param param)))
    ', conT(funT, [baseT(numT), baseT(numT)]), DEBUG)
  end
  fun test-app():
    TEST_INFER_PASS('
      ((fun (param) param) 99)
    ', baseT(numT), DEBUG)
    TEST_INFER_PASS('
      ((fun (param) "hello") 99)
    ', baseT(strT), DEBUG)
    TEST_INFER_FAIL('
      ((fun (param) "hello") param)
    ', "unbound identifier: param", DEBUG)
    TEST_INFER_FAIL('
      ((fun (param) unbound) "hello")
    ', "unbound identifier: unbound", DEBUG)
  end
  fun test-uop():
    TEST_INFER_PASS('
      (empty? empty)
    ', baseT(numT), DEBUG)
    TEST_INFER_PASS('
      (empty? (link "hello" empty))
    ', baseT(numT), DEBUG)
    TEST_INFER_PASS('
      (rest (link 3 (link "hello" empty)))
    ', conT(listT, [baseT(strT), conT(listT, [varT("varT-")])]), DEBUG)
    TEST_INFER_PASS('
      (first (link 3 (link "hello" empty)))
    ', baseT(numT), DEBUG)
  end
  test-bop()
  test-link()
  test-fun()
  test-let()
  test-cif()
  test-app()
  test-uop()
end
