Implementing a Type Checker for Paret

In this assignment, you will implement a type checker for a language called Paret-with-types. Paret-with-types is simply Paret-with-records augmented with type annotations at binding sites.

1 Your Task

You will complete a function called type-of that takes a Paret program, and either returns the type of that program or – if the program is not well-typed – raises an exception. To give some simple examples, type-of("(+ 2 3)") returns numT, and type-of("(2 3)") raises an exception.

type-of is defined to parse its input and then call type-of-full. You will implement type-of-full. It takes a Paret program represented as an Expr, and a TypeEnv that maps identifiers to their types, and either produces the program’s Type or raises an exception. The type environment is necessary to keep track of the types of identifiers that are in scope.

1.1 Types

In the concrete syntax, the type of numbers is written num and the type of strings is written str. Record types are written like (record (x num) (y str)), in which x and y are the field names of the record and num and str are their types. Arrow types (i.e. function types) are written like (num str -> num), where the types before the arrow are the parameter types, and the type after the arrow is the result type.

(Make sure not to confuse record types, represented by recordTs, with record expressions, represented by recordEs. E.g., the record expression (record (a 1)) has type (record (a num)).)

1.2 Annotations

Function definitions and let expressions are now annotated with the types of their arguments/identifiers. For instance, the function that adds one to its argument could be written,

(let ((one : num) 1) (fun ((x : num)) (+ x 1)))
See the grammar for reference.

1.3 Type Checking

There are many options available when choosing how to type check. For this assignment, here are some details on how you should treat the following expression types:
Assignments. An assignment’s subexpression must be a subtype of the type of the variable being assigned to; you must raise an exception otherwise. A variable does not change type after an assignment; it retains the type it was declared as. The type of an assignment expression is the type of the variable being assigned into.

If Statements. Both of an if statement’s branches must have equivalent types. Specifically, both of its branches must be subtypes of the other. Raise an exception otherwise.

Application. Your type checker must raise an exception if a function is applied to the wrong number of arguments, or if a non-function is applied.

Do Statements. The type of a do statement is the type of its last subexpression.

Functions. Functions in Paret-with-types are subtypes when they are identical types.

Identifiers. Your type checker must raise an exception upon encountering an unbound identifier.

1.4 Subtyping

Your type checker must handle record subtyping. One record r1 is a subtype of another r2 when
Every field in r2 is also in r1, and

The type of every field in r1 is a subtype of the type of the field of the same name in r2

(In other words, you will be implementing both width and depth subtyping for records.)
When checking that a function or let argument has the expected type, an exact match is not required: any subtype will do. So, for instance,

((fun ((x : (record (a num)))) x) (record (a 3) (b "four")))
type-checks with type (record (a num)).

You do not need to implement function subtyping, and must not write test cases that assume it will be implemented.

2 Test Cases

You should write your test cases in terms of type-of. The new grammar is more complex than the old one, so try running parse(read-sexpr(<test-program>)) in the interactions window when you are unsure if you have the syntax right.

Do not write test cases that return recTs, since different implementations may store fields in different orders.

As always, only write test cases that conform to the grammar.

3 The New Grammar

Here are the extended data definitions:

>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

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

>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

And the extended grammar:

>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

<expr> ::= <num>
         | <string>  // strings, surrounded by double quotes ""
         | <id>
         | (+ <expr> <expr>)   // addition
         | (- <expr> <expr>)   // subtraction
         | (++ <expr> <expr>)  // string append
         | (== <expr> <expr>)  // string equality
         | (if <expr> <expr> <expr>)
         | (let (<binding> <expr>) <expr>)
         | (fun (<binding> ...) <expr>)
         | (<expr> <expr> ...) // application
         | (assign <id> <expr>)
         | (do <expr> <expr> ...)
         | (record <field> ...) // each field must have a different name
         | (lookup <expr> <id>)
         | (extend <expr> <id> <expr>)
 
<binding> ::= (<id> : <type>)
 
<type> ::= num
         | str
         | (<type> ... -> <type>)
         | (record (<id> <type>) ...)
 
<field> ::= (<id> <expr>)   // field name, followed by field value

>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>


Your job is to fill in this template. If you like Captain Teach and working in the browser, feel free to develop here, but be warned that this may be a longer program than other assignments, which may take a long time to run in your browser. If you’d rather not use Captain Teach, you can work offline and just upload a file below this template. There won’t be any reviews for this assignment.

If you do both, we will take the file over the submission in the editor as your final solution.

