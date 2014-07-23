In this assignment, you will extend your previous calculate-locals function to work over Paret-with-with expressions.

1 Your Task

1.1 Calculate Locals

Your calculate-locals function must return precisely the set of identifiers that are in scope at the hole. In particular, replacing a hole with any one of the identifiers returned by calculate-locals must never cause an unbound identifier exception. Contrariwise, every identifier not in the set returned by calculate-locals must be unbound at that position (though it may not result in a runtime exception, because it may never be evaluated).

The concrete syntax and abstract syntax are identical to that of Paret-with-with, but have been extended with "holes". As before, holes are written as @ in the concrete syntax, and are constructed with hole in the abstract syntax.

1.2 Test Cases

Please write your tests cases in terms of parse-and-calc – it will make them easier to read.

As before, do not write test cases that include no holes or more than one hole. In general, never write test cases of syntactically invalid inputs.

1.3 The Language

For reference, here is the extended grammar:

<expr> ::= <num>
         | <string>  // strings, surrounded by double quotes ""
         | <id>
         | (+ <expr> <expr>)   // addition
         | (- <expr> <expr>)   // subtraction
         | (++ <expr> <expr>)  // string append
         | (== <expr> <expr>)  // string equality
         | (if <expr> <expr> <expr>)
         | (let (<id> <expr>) <expr>)
         | (fun (<id> ...) <expr>)
         | (<expr> <expr> ...) // application
         | (assign <id> <expr>)
         | (do <expr> <expr> ...)
         | (record <field> ...) // each field must have a different name
         | (lookup <expr> <id>)
         | (extend <expr> <id> <expr>)
         | (with <expr> <expr>)
 
         | @                 // a "hole"
 
<field> ::= (<id> <expr>)   // field name, followed by field value


data Expr:
  | idE(name :: String)
  | numE(value :: Number)
  | strE(value :: String)
  | bopE(op :: Operator, left :: Expr, right :: Expr)
  | cifE(cond :: Expr, consq :: Expr, altern :: Expr)
  | letE(name :: String, expr :: Expr, body :: Expr)
  | lamE(params :: List<String>, body :: Expr)
  | appE(func :: Expr, args :: List<Expr>)
  | assignE(name :: String, expr :: Expr)
  | doE(exprs :: List<Expr>)
  | recordE(fields :: List<Field>)
  | lookupE(rec :: Expr, field-name :: String)
  | extendE(rec :: Expr, field-name :: String, new-value :: Expr)
  | withE(namespace :: Expr, body :: Expr)

  | holeE
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
        letE(sexpr.get(1).get(0),
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
      else if head == "with":
        withE(convert(sexpr.get(1)), convert(sexpr.get(2)))
      else if head == "assign":
        assignE(sexpr.get(1), convert(sexpr.get(2)))
      else if head == "do":
        when is-empty(sexpr.rest):
          raise("Paret: do blocks cannot be empty")
        end
        doE(map(convert, sexpr.rest))
      else if head == "fun":
        lamE(sexpr.get(1), convert(sexpr.get(2)))
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
    else if sexpr == "@":
      holeE
    else if String(sexpr):
      idE(sexpr)
    end
  end
  convert(prog)
end
