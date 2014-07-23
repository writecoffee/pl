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

getloc = fun(): gensym("id") end


fun interp-env(exp :: Expr, env :: Env, store :: Store) -> Result:
  cases(Expr) exp:
    | idE(name) => result(fetch(lookup-env(name, env), store), store)
    | numE(value) => result(numV(value), store)
    | strE(value) => result(strV(value), store)
    | bopE(op, left, right) => binOp(op, left, right, env, store)
    | cifE(cond, consq, altern) =>
        cases(Result) interp-env(cond, env, store):
          | result(val, cond-store) =>
              cases(Value) val:
                | numV(value) =>
                    if value <> 0:
                      interp-env(consq, env, cond-store)
                    else:
                      interp-env(altern, env, cond-store)
                    end
                | else => raise("Test condition must be a number")
              end
        end
    | lamE(params, body) => result(funV(params, body, env), store)
    | appE(func, args) =>
        cases(Result) interp-env(func, env, store):
          |result(cl-val, cl-store) =>
              cases(Value) cl-val:
                | funV(params, body, cl-env) =>
                    when args.length() <> params.length():
                      raise(("Arity error: expected " + params.length().tostring())
                        + (" argument(s), got " + args.length().tostring()))
                    end
                    arg-res = weft(args, env, cl-store)
                    apply(params, arg-res, body, cl-env, cases(List) arg-res:
                                                          | empty => cl-store
                                                          | link(_, _) => arg-res.last().store
                                                         end)
                | else => raise("My dad's not a phone!  And you can only apply lambdas!")
              end
        end
    | recordE(fields) =>
        field-res = weft(map(fun(item): item.value end, fields), env, store)
        result(recV(map2(fun(e-name, e-val): fieldV(e-name, e-val.val) end,
                          map(fun(item): item.name end, fields),
                          field-res)),  cases(List) field-res:
                                          | empty => store
                                          | link(_, _) => field-res.last().store
                                        end)
    | lookupE(rec, field-name) =>
        lookup-res = interp-env(rec, env, store)
        cases(Value) lookup-res.val:
          | recV(fields) => result(rec-lookup(field-name, fields), lookup-res.store)
          | else => raise("Can only perform lookups on records")
        end
    | extendE(rec, field-name, new-value) =>
        extend-res = interp-env(rec, env, store)
        cases(Value) extend-res.val:
          | recV(fields) =>
              new-val-res = interp-env(new-value, env, extend-res.store)
              result(recV(link(fieldV(field-name, new-val-res.val), fields)), new-val-res.store)
          | else => raise("Can only extend records")
        end
  end
end

fun rec-lookup(field-name :: String, rec-fields :: List<FieldV>) -> Value:
  cases(List) rec-fields:
    | empty => raise("Field not Found in record:" + field-name)
    | link(first, rest) => 
        if first.name == field-name:
          first.value
        else:
          rec-lookup(field-name, rest)
        end
  end
end


fun lookup-env(name-id :: String, env :: Env) -> String:
  cases(Env) env:
    | mt-env => raise("Unbound identifier: " + name-id)
    | an-env(name, loc, rest-env) =>
        if name == name-id:
          loc
        else:
          lookup-env(name-id, rest-env)
        end
  end
end


fun fetch(loc-id :: String, store :: Store) -> Value:
  cases(Store) store:
    | mt-store => raise("Something went VERY wrong")
    | a-store(loc, val, rest-store) =>
        if loc-id == loc:
          val
        else:
          fetch(loc-id, rest-store)
        end
  end
end

fun shelve(loc-id :: String, item-val :: Value, store :: Store) -> Store:
  cases(Store) store:
    | mt-store => raise("Something went VERY wrong")
    | a-store(loc, val, rest-store) =>
        if loc-id == loc:
          a-store(loc, item-val, rest-store)
        else:
          a-store(loc, val, shelve(loc-id, item-val, rest-store))
        end
  end
end


fun weft(args :: List<Expr>, arg-env :: Env, store :: Store) -> List<Result>:
  cases(List) args:
    | empty => empty
    | link(first, rest) =>
        cur-arg = interp-env(first, arg-env, store)
        link(cur-arg, weft(rest, arg-env, cur-arg.store))
  end
end

fun apply(params :: List<String>, args :: List<Result>, body :: Block, cl-env :: Env, store :: Store) -> Result:
  new-locations = map(fun(x): getloc() end, args)
  interp-full(body, fold2(fun(clos-env, param-name, new-loc):
                            an-env(param-name, new-loc, clos-env)
                          end, cl-env, params, new-locations),
                    fold2(fun(cl-store, new-loc, arg-val):
                            a-store(new-loc, arg-val.val, cl-store)
                          end, store, new-locations, args))
end

fun binOp(binop :: Operator, left :: Expr, right :: Expr, env :: Env, store :: Store) -> Result:
  cases(Result) interp-env(left, env, store):
    | result(left-val, left-store) =>
        cases(Value) left-val:
          | numV(l-value) =>
              cases(Result) interp-env(right, env, left-store):
                | result(right-val, right-store) =>
                    cases(Value) right-val:
                      | numV(r-value) => 
                          cases(Operator) binop:
                            | plus => result(numV(l-value + r-value), right-store)
                            | minus => result(numV(l-value - r-value), right-store)
                            | else => raise("Invalid operator for numbers")
                          end
                      | else => raise("Argument mismatch: both args must be of the same type")
                    end
              end
          | strV(l-value) =>
              cases(Result) interp-env(right, env, left-store):
                | result(right-val, right-store) =>
                    cases(Value) right-val:
                      | strV(r-value) =>
                          cases(Operator) binop:
                              | append => result(strV(l-value + r-value), right-store)
                              | str-eq => result(numV(if l-value == r-value: 1 else: 0 end), right-store)
                              | else => raise("Invalid operator for strings")
                          end
                      | else => raise("Argument mismatch: both args must be of the same type")
                    end
              end
          | else => raise("Invalid argument for binary op")
        end
  end
end
fun interp-full(prog :: Block, env :: Env, store :: Store) -> Result:
  cases(Block) prog:
    | block(stmts) =>
        new-locations = map(fun(x): getloc() end, filter(is-defvar, stmts))
        var-names = for fold(name-list from empty, defvars from filter(is-defvar, stmts)):
                          when name-list.member(defvars.name): raise("Duplicate variable name in block") end
                          link(defvars.name, name-list)
                    end
        start-env = fold2(fun(lifted-env, var-name, new-loc):
                              an-env(var-name, new-loc, lifted-env)
                          end,
                          env,
                          var-names,
                          new-locations)
        start-store = fold(fun(lifted-store, new-loc):
                    a-store(new-loc, nullV, lifted-store)
                    end,
                    store,
                    new-locations)
        for fold(end-result from result(nullV, start-store), stmt from stmts):
          cases(Stmt) stmt:
            | defvar(name, set-expr) =>
                var-val = interp-env(set-expr, start-env, end-result.store)
                result(var-val.val, shelve(lookup-env(name, start-env), var-val.val, var-val.store))
            | assign(name, set-expr) =>
                var-val = interp-env(set-expr, start-env, end-result.store)
                result(var-val.val, shelve(lookup-env(name, start-env), var-val.val, var-val.store))
            | expr-stmt(body-expr) => interp-env(body-expr, start-env, end-result.store)
          end
        end
  end



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
  eval('
    (lookup (record (x 1) (y 3)) not-exist-id)
  ') raises "" # "record field: not-exist-id not found"
  eval('
    (extend (record (x 1) (y 3)) not-exist-id)
  ') raises "" # "record field: not-exist-id not found"
  eval('
    (lookup (fun () 3) not-exist-id)
  ') raises "" # "lookupE: input cannot be evaluated to a record value"
  eval('
    (extend "something not a record" z 9)
  ') raises "" # "extendE: input cannot be evaluated to a record value"
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
  eval('
    (defvar my-record (record (x 1) (y 3)))
    (lookup my-record x)
  ') is numV(1)
  eval('
    (defvar my-record (record (x 1) (y 3)))
    (lookup (extend my-record z 9) z)
  ') is numV(9)
  eval('
    (defvar my-record (record (x 1) (y 3)))
    ((fun (a1 a2)
          (assign my-record (record (x 99) (y 999)))
          (+ a1 (- a2 (lookup my-record x))))
     0 0)
  ') is numV(-99)
  eval('
    (defvar my-record (record (x 1) (y 3)))
    (defvar my-func (fun (a1 a2 a3) (+ a1 (+ a2 a3))))
    (defvar ur-record my-record)
    (assign my-record (record (x 0) (y 999)))
    (my-func (lookup my-record x)
             (lookup ur-record x)
             (lookup my-record y))
  ') is numV(1000)
  eval('
    (defvar myFun 
            (fun (x) (assign x 99)
                     (assign x 77)))
    (myFun 9)
  ') is numV(77)
  eval('
    (defvar myFun 
            (fun (x) (assign x 99)
                     (defvar x 77)))
    (myFun 9)
  ') is numV(77)
end
