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

data ListFieldVStore:
  |fieldVlist-store(fieldvlist :: List<FieldV>, store :: Store)
end

data EnvStoreStmts:
  |env-store-stmts(env :: Env, store :: Store, stmts :: List<Stmt>)
end

#helper function that gets the location of an identifier in the environment
fun lookup(s :: String, env :: Env)->String:
  cases (Env) env:
    |mt-env=> raise("unbound identifier: " + s)
    |an-env(name,loc,nv) =>
      if s == name:
        loc
      else:
        lookup(s,nv)
      end
  end
end

#helper function that gets value stored in a location
fun fetch(location :: String, store :: Store)->Value:
  cases (Store) store:
    |mt-store => raise("uninitialized value")
    |a-store(loc,val,st) =>
      if location == loc:
        val
      else:
        fetch(location,st)
      end
  end
end

#helper function to get the value of a field-name in a record
fun lookup-help(fields :: List<FieldV>, field :: String)->Value:
  cases(List<FieldV>) fields:
    |empty => raise("field: " + field + " not found on record")
    |link(f,r)=>
      if field == f.name:
        f.value
      else:
        lookup-help(r,field)
      end
  end
end
  
fun check-duplicate-fields(fieldlist :: List<Field>, fields :: Set<String>)-> List<String>:
  cases (List<Field>) fieldlist:
   | empty => []
   | link(f,r) => 
     if fields.member(f.name):
       raise("field names in recV must be unique")
     else:
       new-fields = fields.add(f.name)
       check-duplicate-fields(r,new-fields)
     end
   end
end

fun records-help(fieldlist :: List<Field>, nv :: Env, st :: Store, fieldVlist :: List<FieldV>)-> ListFieldVStore:
  check-duplicate-fields(fieldlist, set([]))
  cases (List<Field>) fieldlist:
      |empty=> fieldVlist-store(fieldVlist,st)
      |link(f,r)=>
        value= interp-expr(f.value, nv,st)
        new-fieldV = fieldV(f.name, value.val)
        new-fieldVlist = link(new-fieldV,fieldVlist)
        records-help(r,nv, value.store,new-fieldVlist)
  end
end

fun interp-expr(prog :: Expr, env :: Env, store :: Store) ->Result:
  cases (Expr) prog:
    | nullE => result(nullV,store)
      #For num and string we simply return the value and
      #pass the same store
    | numE(n)=> result(numV(n), store)
    | strE(s)=> result(strV(s), store)
      #for iDE we need to lookup and fetch, but store
      #remains unchanged
    | idE(x) => result(fetch(lookup(x, env), store),store)
    | bopE(op, l, r) =>
     #all operators follow the same pattern: evaluate 
      #left, evaluate right (with left's updated store), 
      #and do pyret's operations on the values from left 
      #and right with right's store
      left = interp-expr(l, env, store)
      right = interp-expr(r, env, left.store)
      cases (Operator) op:
        |plus=> 
          cases (Value) left.val:
            |numV(n) =>
              cases (Value) right.val:
                |numV(n2) => result(numV(n + n2), right.store)
                |else => raise("Type mismatch. Expected numV")
              end
            |else =>raise("Type mismatch. Expected numV")
          end
        |minus =>
          cases (Value) left.val:
            |numV(n) =>
              cases (Value) right.val:
                |numV(n2) => result(numV(n - n2), right.store)
                |else => raise("Type mismatch. Expected numV")
              end
            |else =>raise("Type mismatch. Expected numV")
          end
        |append=>
          cases (Value) left.val:
            |strV(n) =>
              cases (Value) right.val:
                |strV(n2) => result(strV(n + n2), right.store)
                |else => raise("Type mismatch. Expected strV")
              end
            |else =>raise("Type mismatch. Expected strV")
          end
        |str-eq=>
          cases (Value) left.val:
            |strV(n) =>
              cases (Value) right.val:
                |strV(n2) => 
                  if n==n2:
                    result(numV(1), right.store)
                  else:
                    result(numV(0), right.store)
                  end
                |else => raise("Type mismatch. Expected strV")
              end
            |else =>raise("Type mismatch. Expected strV")
          end
      end
    | cifE(cond, conq, altern)=>
      #here we evaluate the conditional and evaluate
      #the branches with the store from the conditional
      condi = interp-expr(cond,env, store)
      cases (Value) condi.val:
        |strV(s) =>raise("Type mismatch. Expected numV and got strV")
        |numV(num) =>
          if num==0:
            interp-expr(altern,env, condi.store)
          else:
            interp-expr(conq,env, condi.store)
          end
      end
    | lamE(params, body)=> 
      result(funV(params, body, env), store)
    | appE(func, args) => 
      funct = interp-expr(func,env,store)
      cases (Value) funct.val:
        | funV(params, body, closure)=>
          params-num = params.length()
          args-num = args.length()
          if params-num == args-num:
            #create a list of locations to be added to 
            #env and store
            new-locs = for map(i from params):
              gensym("loc")
            end
            #bound the params to the locations
            new-env = for fold2(c from closure, p from params, l from new-locs):
              an-env(p,l,c)
            end    
            #evaluate each args and add the corresponding 
            #val to the store, making sure to use each 
            #previous evaluation store.
            new-store = for fold2(s from store, a from args, l from new-locs):
              new-val = interp-expr(a,env,s)
              a-store(l, new-val.val,new-val.store)
            end 
            
            #evaluate the body using new env and new 
            #store
            evaluate = interp-full(body,new-env,new-store)
            result(evaluate.val,evaluate.store)
          else:
            raise("incorrect numbers of params passed to function") 
          end
        | else=>raise("you can only apply arguments to functions")
      end
    | recordE(fields)=>
      res = records-help(fields, env, store, [])
      result(recV(res.fieldvlist), res.store)
    | lookupE(rec, field-name)=>
      rec-v = interp-expr(rec,env,store)
      cases(Value) rec-v.val:
        |recV(fields)=>      
          result(lookup-help(fields, field-name),store)
        |else=> 
          raise("lookup expected a recV but got: "+rec-v.val)
      end
      
    | extendE(rec, field-name, new-value)=>
      #I handle adding new-value with existing field-name 
      #by simply adding it to the top. lookup will return
      #the newest one
      rec-v = interp-expr(rec,env,store)
      cases(Value) rec-v.val:
        |recV(fields)=>
          new-field-value = interp-expr(new-value, env,rec-v.store)
          new-field = fieldV(field-name, new-field-value.val)
          new-fields = link(new-field, fields)
          result(recV(new-fields),new-field-value.store)
        |else=> raise("extend expected a recV but got: "+rec-v.val)
      end
  end   
end

fun interp-stmt(stmt :: Stmt, env :: Env, store :: Store) ->Result:
  cases(Stmt) stmt:
    |defvar(name,expr) =>
      print("inside defvar")
    |assign (name, expr) => 
      new-val = interp-expr(expr, env, store)
      var-loc = lookup(name, env)
      new-store = a-store(var-loc, new-val.val, new-val.store)
      result(new-val.val, new-store)
    |expr-stmt(expr)=> interp-expr(expr, env, store)
  end
end
 
fun bind-vars-stmts(prog :: List<Stmt>, env :: Env, store :: Store, new-prog :: List<Stmt>)->EnvStoreStmts:
  cases(List<Stmt>) prog:
    |link(f,r)=>
      cases(Stmt) f:
        |defvar(name, expr)=>
          try:
            value = fetch(lookup(name,env),store)
            if value == nullV:
            raise("cannot have more than one defvar in the same block")
            else:
              newprog = link(assign(name,expr),new-prog)
              if r.length()>0:
            bind-vars-stmts(r, env,store, newprog)
            else:
              env-store-stmts(env,store, newprog)
            end
            end
            except(exception):
            if exception <> "cannot have more than one defvar in the same block":  
              location = gensym("loc")
              new-env = an-env(name, location, env)
              new-store = a-store(location, nullV, store)
              newprog = link(assign(name, expr), new-prog)
            if r.length()>0:
            bind-vars-stmts(r, new-env, new-store, newprog)
            else:
              env-store-stmts(new-env,new-store, newprog)
            end
            else:
              raise("cannot have more than one defvar in the same block")
              end  
          end  
        |else =>
          newprog = link(f, new-prog)
          if r.length()>0:
            bind-vars-stmts(r,env, store, newprog)
          else:
            env-store-stmts(env,store, newprog)
          end 
      end
    end
end

fun interp-stmts(stmts :: List<Stmt>, env :: Env, store :: Store) -> Result:
  cases(List<Stmt>) stmts:
    |link(f,r)=>
      first-stmt = interp-stmt(f, env, store)
      if r.length() ==0:
        first-stmt
      else:
        interp-stmts(r,env,first-stmt.store)
      end
    end
end

fun interp-full(prog :: Block, env :: Env, store :: Store) -> Result:
  new-env-store-stmts = bind-vars-stmts(prog.stmts, env, store, [])
  interp-stmts(new-env-store-stmts.stmts.reverse(), new-env-store-stmts.env, new-env-store-stmts.store)
where:
  eval('(defvar x 1) (defvar x 2)') raises ""
    #Numbers
  eval("1") is numV(1)
  eval("2") is numV(2)
  
  #Strings
  eval("\"string\"") is strV("string")
  eval("\"\"") is strV("")
  
  
  #Simple Binary operations
  eval("(+ 2 4)") is numV(6)
  eval("(+ 3 4)") is numV(7)
  eval("(++ \"string\" \"string\")") is strV("stringstring")
  eval("(- 2 1)") is numV(1)
  eval("(- 3 3)") is numV(0)
  eval("(++ \"one\" \"two\")") is strV("onetwo")
  eval("(++ \"one\" \"\")") is strV("one")
  eval("(- (+ 5 1) 4)") is numV(2)
  eval("(== \"one\" \"two\")") is numV(0)
  eval("(== \"string\" \"string\")") is numV(1)
  
  #exceptions with binary operations
  eval("(+ 1)") raises ""
  eval("(+ 3 \"string\")") raises ""
  eval("(- \"string\" \"string\")") raises "" 
  eval("(- 1)") raises ""
  eval("(++ 2 2)") raises ""
  eval("(== 2 2)") raises ""
  
  #conditionals
  eval("(if 0 2 0)") is numV(0)
  eval("(if 1 1 0)") is numV(1)
  eval("(if (== \"one\" \"one\") 1 0)") is numV(1)
  eval("(if \"one\" 1 0)") raises ""
  
  #let statements
  eval("(defvar x 3) (+ x 1)") is numV(4)
  eval("(defvar x (fun (a b) (+ a b))) (x 1 2)") is numV(3)
  eval("(defvar x 3) (defvar y 4) (+ x y)") is numV(7)
  eval("(defvar x 3) (defvar y 4) y") is numV(4)
  eval("(defvar x 3) (defvar y 4) x") is numV(3)
  eval("(defvar x (fun (a b) (+ a b))) (x 1)") raises ""
  eval("(defvar x (fun (a b) (_ a b))) (x 1 2 3))") raises ""
  eval("(defvar x x) x") is nullV #is this true??
  
  #functions
  eval("(+ (fun (x) x) 3)") raises ""
  eval("((fun (x) (+ x 1)) 1)") is numV(2)
  eval("(defvar three (fun () 3)) (three)") is numV(3)
  eval("((fun (x) (defvar x 3) (+ x 1)) 1)") is numV(4)
  eval("(defvar x 5) ((fun (x) (+ x 2)) 1)") is numV(3)
  eval("(defvar x (fun (a b) (+ a b))) (defvar y (fun (a b) (- a b))) (x 10 (y 2 1))") is 
 numV(11)
 eval("(fun (x) x)") is funV(["x"], block([expr-stmt(idE("x"))]), mt-env) 
  eval("(defvar x 1) (defvar x 2)") raises ""
  eval("(defvar x 1) ((fun () (defvar x (+ x 1)) x))") is numV(2)
  
  #assign
  eval("(defvar x 3) (assign x 5) x") is numV(5)
  eval("(defvar x 2) (assign x 3) (defvar y x) (+ x y)") is numV(6)
  eval("(defvar x 3) (assign x 0) (if x 1 x)") is numV(0)
  eval("(defvar x 3) (assign x 1) (if x x 0)") is numV(1)
  eval("(defvar x 3) (assign x \"string\") x") is strV("string")
  eval("(defvar x 3) (assign x x) x") is numV(3)
  eval("(defvar x \"string\") (assign x 1) x") is numV(1)
  eval("(defvar x 1) (assign x (+ 1 1))") is numV(2)
  
  eval("(defvar x 1) (assign x (+ x 1)) x") is numV(2)
  eval("(defvar x 1) (assign x a)") raises ""
  eval("1 2 3") is numV(3)
  eval("(+ 1 1) (+ 2 2) (+ 3 3)") is numV(6)
  
  eval("((fun (x) (defvar x 3) x) 1)") is numV(3) 
  eval("(defvar x 1) (assign x 3) x") is numV(3)
  eval("(defvar x 1) (assign x (+ x 1)) (assign x (+ x 1)) x") is numV(3)
  
  eval("(defvar x 3) (defvar y 2) (assign x y) x") is numV(2)
  eval("(defvar x 3) ((fun (x) (+ x 1)) 1)") is numV(2)
  eval("(defvar x 3) (defvar y 2) (assign y x) (assign x 5) y") is numV(3)
  eval("
     (defvar x 1)
     ((fun () (defvar x 2) (assign x 3)))
     x
  ") is numV(3)
  eval("(defvar x 0) (+ ((fun () (assign x (+ x 1)))) ((fun () (assign x (+ x 1)))))") is numV(3)
 
  eval("((fun (x y) (assign x 3) (+ x y)) 1 2)") is numV(5)
  
   #fun with mutation
 eval("(defvar x 1) (+ ((fun () (assign x (+ x 1)) x)) ((fun () (assign x (+ x 1)) x)))") is numV(5)
 eval("(defvar x 1) (if ((fun () (assign x 0))) 1 x)") is numV(0)
 eval("(defvar x 1) ((fun (y) (+ x y)) ((fun () (assign x 2) 3)))") is numV(5)
 eval("(defvar x 1) ((fun (y z) (+ y z)) ((fun () (assign x 2) 1)) x)") is numV(3)
 eval("(defvar x 1) (defvar y (record (a ((fun () (assign x 2) 1))))) (+ (lookup y a) x)") is numV(3)
 
 
 eval("(defvar x 1) (lookup (extend ((fun () (assign x 2) (record))) a x) a)") is numV(2)
 eval("(defvar x 1) (defvar y ((fun () (assign x 2) 5))) x") is numV(2)
 eval("(defvar x 1) (defvar y 1) (assign y ((fun () (assign x 2) 3))) (+ x y)") is numV(5)
 
 #records
 eval("(defvar x (record (x 1) (y 2) (z 3))) (lookup x x)") is numV(1)
 eval("(defvar x (record (x 1) (y 2) (z 3))) (lookup x y)") is numV(2)
 eval("(defvar x (record (x 1) (y 2) (z 3))) (lookup x z)") is numV(3)
 eval("(defvar x (record (x \"string\"))) (lookup x x)") is strV("string")

 eval("(defvar x (record (x 1))) ((fun () (defvar x (record (x 2))) (lookup x x)))") is numV(2)
 eval("(defvar x (record)) (assign x (extend x y 1)) (lookup x y)") is numV(1)
 eval("(defvar x (record)) (lookup x y)") raises ""
 eval("(defvar x (record (a 1))) (defvar y (extend x a (+ (lookup x a) 1))) (lookup y a)") is numV(2)
 eval("(defvar x 3) (defvar y (record (x x))) (lookup y x)")is numV(3)
 eval("(defvar x (record (a (record (b 1))))) (lookup (lookup x a) b)") is numV(1)
 eval("(defvar x (record (a 1))) (assign x (extend x x x)) (lookup (lookup x x) a)") is numV(1)
 eval("(defvar x (record (func (fun (x) x)))) ((lookup x func) 1)") is numV(1)
 eval("(defvar x 3) (defvar y (record)) (assign y ((fun () (assign x 2) (extend y x x)))) (lookup y x)") is numV(2)
 eval("(lookup x a)") raises ""
 eval("(defvar x 3) (lookup x a)") raises ""
 eval("(defvar x \"string\") (lookup x a)") raises ""
 eval("(defvar x 3) (extend x a 1)") raises ""
 eval("(defvar x \"string\") (extend x a 1)") raises ""
 eval("(extend x a 1)")raises ""
 eval("(extend (record) a b)") raises ""
 eval("(lookup 1 b)") raises ""
 eval("(extend 1 a 2)") raises ""
 eval("(lookup (record) 1)") raises ""
 eval("(extend (record) 1 1)") raises ""
 eval("null") is nullV
 
 #defvar quirks
 eval("(+ x 1) (defvar x 1)") raises ""
 eval("(defvar y (fun () x)) (defvar x 1) (y)") is numV(1)
 eval("(defvar y (fun () x)) (defvar result (y))") raises ""

 eval("(assign x 1) (defvar x 2) x") is numV(2)
 eval("(defvar result ((fun () (assign x 1) x ))) (defvar x 3) result") is numV(1)
 eval("(assign x 2) (defvar x (+ x 2)) x") is numV(4)
 eval("(defvar x y) (defvar y 1) x") is nullV
 eval("(defvar x y) (defvar y x) y") is nullV
 eval("(defvar x y) (defvar y x) x") is nullV
 eval('(defvar x 1) ((fun (y) (defvar x 2) (+ y x)) 1)') is numV(3)
 eval('(defvar x 1) (defvar x 2)') raises ""
 
 #interpreting defvars and assigns
 eval("(defvar x 1)") is numV(1)
 eval("(defvar x 1) (assign x 2)") is numV(2)
 
  
 eval("((fun (x) (defvar x 3) (+ x 1)) 1)") is numV(4) 
 eval("(defvar x 3) (assign x (+ x 1)) ((fun () (defvar x 4) x))") is numV(4)
 eval('(assign x 2) (defvar x 10) x') is numV(10)
  
 eval("(defvar y (fun () x)) (defvar result (y)) (defvar x 1)") is numV(1)
end
