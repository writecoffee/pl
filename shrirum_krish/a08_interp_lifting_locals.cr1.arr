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

fun lookup(name :: String, env :: Env) -> String:
  doc: "Get l-value for identifier 'name'"
  cases(Env) env:
    | mt-env => raise("Unbound identifier " + name)
    | an-env(f-name, f-loc, rest-env) =>
      if f-name == name:
        f-loc
      else:
        lookup(name, rest-env)
      end
  end
end

fun fetch(lval :: String, store :: Store) -> Value:
  doc: "Given an l-val, return the value stored at that l-value in the store."
  cases(Store) store:
    | mt-store => raise("Identifier in env without corresponding binding in store")
    | a-store(loc, val, r-store) =>
      if loc == lval:
        val
      else:
        fetch(lval, r-store)
      end
  end
end

fun handle-binary-operator(operator :: Operator, left :: Expr, right :: Expr, env :: Env, store :: Store) -> Result:
  doc: "Helper function for correctly matching+handling an Operator with arguments."
  left-result = handle-expr(left, env, store)
  right-result = handle-expr(right, env, left-result.store)
  cases(Operator) operator:
    | plus =>
      result(numV(left-result.val.value + right-result.val.value), right-result.store)
    | minus =>
      result(numV(left-result.val.value - right-result.val.value), right-result.store)
    | append =>
      result(strV(left-result.val.value + right-result.val.value), right-result.store)
    | str-eq =>
      strings-are-equal = strV(left-result.val.value).value == strV(right-result.val.value).value
      if strings-are-equal:
        result(numV(1), right-result.store)
      else:
        result(numV(0), right-result.store)
      end
  end
end

fun handle-cond-expr(cond :: Expr, then-stmt :: Expr, else-stmt :: Expr, env :: Env, store :: Store) -> Result:
  doc: "Helper function for dealing with conditional statements."
  cond-result = handle-expr(cond, env, store)
  if numV(cond-result.val.value).value == 0:
    handle-expr(else-stmt, env, cond-result.store)
  else:
    handle-expr(then-stmt, env, cond-result.store)
  end
end

# Necessary for recursive building of env/store in evaluation
# of arguments in app
data EnvStorePair:
  | env-store-pair(env :: Env, store :: Store)
end

fun build-env-and-store(params :: List<String>, args :: List<Expr>, env :: Env, store :: Store, parent-scope-env :: Env) -> EnvStorePair:
  doc: "Given a list of params and args, create bindings in env such that first elt of parmas is bound to the value of the first elt in args, etc."
  cases(List) params:
    | empty =>
      if args <> empty:
        raise("Improper number of arguments.")
      else:
        env-store-pair(env, store)
      end
    | link(f-param, r-param) =>
      cases(List) args:
        | empty => raise("Improper number of arguments.")
        | link(f-arg, r-arg) =>
          # By passing in the parent's scope we do not pollute
          # the environment of nested expressions.
          this-arg-result = handle-expr(f-arg, parent-scope-env, store)
          new-loc = gensym('loc')
          build-env-and-store(r-param, r-arg, an-env(f-param, new-loc, env), a-store(new-loc, this-arg-result.val, this-arg-result.store), parent-scope-env)
      end
  end
end

fun handle-app-expr(func :: Expr, args :: List<Expr>, env :: Env, store :: Store) -> Result:
  doc: "Helper function for dealing with app statements."
  # Reinterpret the function with params bound to the envrionment.
  function-result-without-subst = handle-expr(func, env, store)
  
  env-and-store-after-args = build-env-and-store(function-result-without-subst.val.params, args,   function-result-without-subst.val.env, store, env)
  
  interp-full(function-result-without-subst.val.body, env-and-store-after-args.env, env-and-store-after-args.store)
end

fun handle-assign(name :: String, expr :: Expr, env :: Env, store :: Store) -> Result:
  doc: "Helper function for dealing with assign"
  expr-result = handle-expr(expr, env, store)
  loc-of-name = lookup(name, env)
  new-store = a-store(loc-of-name, expr-result.val, expr-result.store)
  result(expr-result.val, new-store)
end

fun handle-record(fields :: List<Field>, env :: Env, store :: Store, list-of-fieldV :: List<fieldV>) -> Result:
  doc: "Helper function for handling records"
  cases(List) fields:
    | empty => result(recV(list-of-fieldV), store)
    | link(f-field, r-fields) =>
      # fieldE(name, value)
      f-field-expr-result = handle-expr(f-field.value, env, store)
      # add to end of accumulator
      updated-fieldV-accumulator = list-of-fieldV + [fieldV(f-field.name, f-field-expr-result.val)]
      handle-record(r-fields, env, f-field-expr-result.store, updated-fieldV-accumulator)      
  end
end

fun search-record(record :: List<fieldV>, name :: String) -> Value:
  doc: "Given a list of fieldV, find the fieldV with name field equal to provided name, and return the associated value."
  cases(List) record:
    | empty => raise("Error: field name not found in record")
    | link(f-field, r-fields) =>
      if f-field.name == name:
        f-field.value
      else:
        search-record(r-fields, name)
      end
  end
end

fun handle-rec-lookup(record :: Expr, field-name :: String, env :: Env, store :: Store) -> Result:
  doc: "Helper function for looking up in a record"
  # Note that fields are added to the end of the list in the order
  # in which they're encountered. For example, 
  # (record (y 1) (x 2)) -> [fieldV(y, numV(1)), fieldV(x, numV(2))]
  record-result = handle-expr(record, env, store)
  result(search-record(record-result.val.fields, field-name), record-result.store)  
end

fun handle-extend-rec(record :: Expr, field-name :: String, new-value :: Expr, env :: Env, store :: Store) -> Result:
  doc: "Helper function for extending a record"
  record-result = handle-expr(record, env, store)
  new-value-result = handle-expr(new-value, env, record-result.store)
  old-record-fields = record-result.val.fields
  # We add 'updated' records to the front of the list, because
  # search-record begins at the front of the list. We want
  # the most-recent record at the front of the list.
  new-record-fields = [fieldV(field-name, new-value-result.val)] + old-record-fields
  result(recV(new-record-fields), new-value-result.store)
end

fun handle-expr(expr :: Expr, env :: Env, store :: Store) -> Result:
  cases(Expr) expr:
    | nullE => result(nullV, store)
    | numE(n) => result(numV(n), store)
    | strE(s) => result(strV(s), store)
    | idE(name) => result(fetch(lookup(name, env), store), store)
    | bopE(op, left, right) =>
      handle-binary-operator(op, left, right, env, store)
    | cifE(cond, then-stmt, else-stmt) =>
      handle-cond-expr(cond, then-stmt, else-stmt, env, store)
    | lamE(params, body) =>
      result(funV(params, body, env), store)
    | letE(name, expression, body) =>
      expression-result = handle-expr(expression, env, store)
      new-loc = gensym('loc')
      handle-expr(body, an-env(name, new-loc, env), a-store(new-loc, expression-result.val, expression-result.store))
    | appE(func, args) =>
      handle-app-expr(func, args, env, store)
    | recordE(fields) =>
      handle-record(fields, env, store, empty)
    | lookupE(rec, field-name) =>
      handle-rec-lookup(rec, field-name, env, store)
    | extendE(rec, field-name, new-value) =>
      handle-extend-rec(rec, field-name, new-value, env, store)
  end
end

fun handle-single-stmt(stmt :: Stmt, env :: Env, store :: Store) -> Result:
  cases(Stmt) stmt:
    | expr-stmt(expr :: Expr) =>
      handle-expr(expr, env, store)
    | assign(name, expr) =>
      handle-assign(name, expr, env, store)
    | defvar(name, expr) =>
      # lift-defvar has already bound 'name' in
      # this environment. Now, we can treat all
      # defvar's as assigns.
      handle-assign(name, expr, env, store)
  end
end

fun lift-defvar(bl :: Block, env :: Env, store :: Store, lifted-vars :: Set<String>) -> EnvStorePair:
  doc: "Given a block, iterate over the list of statements. When encountered with a defvar, assign the value to null. Note that this is called before evaluation of terms."
  cases(Block) bl:
    | block(stmt-list) =>
      cases(List) stmt-list:
        | empty => env-store-pair(env, store)
        | link(f-stmt, r-stmt) =>
          cases(Stmt) f-stmt:
            | defvar(name, expr) =>
              if lifted-vars.member(name):
                raise("Error: defvar'ing same identifier in same scope twice")
              else:
                # Assign to null
                env-and-store-with-lift = build-env-and-store([name], [nullE], env, store, env)
                lift-defvar(block(r-stmt), env-and-store-with-lift.env, env-and-store-with-lift.store, lifted-vars.add(name))
              end
            | else => lift-defvar(block(r-stmt), env, store, lifted-vars)
          end
      end
  end
end

fun handle-block(bl :: Block, env :: Env, store :: Store) -> Result:
doc: "This handles blocks. interp-full could serve the same purpose, but I like the idea of creating an explicitly named function."
  cases(Block) bl:
    | block(stmt-list) =>
      cases(List) stmt-list:
        | empty => raise("Error: Empty block.")
        | link(f-stmt, r-stmt) =>
          if r-stmt.length() == 0:
            handle-single-stmt(f-stmt, env, store)
          else:
            f-stmt-result = handle-single-stmt(f-stmt, env, store)
            handle-block(block(r-stmt), env, f-stmt-result.store)
          end
      end
  end
end

fun interp-full(prog :: Block, env :: Env, store :: Store) -> Result:
  lifted-env-store-pair = lift-defvar(prog, env, store, set([]))
  handle-block(prog, lifted-env-store-pair.env, lifted-env-store-pair.store)
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
