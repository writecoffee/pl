Implementing an Interpreter - Adding Records

In this assignment, you will add records to the Paret language. You may refer to the new language as Paret-with-records. This assignment builds off of the last one, so the language still contains assign and do expressions.

1 The Extended Language

A recV (for "record") value has been added, and the grammar and Expr data type have been extended with three new forms.

1.1 record

A record expression constructs a record value out of the given fields. Each of the fields’ contents should be evaluated in order, and then a recV value should be constructed from the values produced. You may assume that the field names in a record expression are all distinct, and should avoid writing test cases in which they are not. For instance, don’t write test cases involving (record (x 1) (x 2)).

1.2 lookup

lookup looks up a field name on a record value. It has an expression rec and a field name field-name (represented as a string). It evaluates the rec, and, assuming the result is a recV, finds and returns the (first) field named f on it. An exception should be raised if either rec does not evaluate to a recV or if field-name can not be found on that recV.

1.3 extend

extend extends a record value by adding a new field on to it. It has an expression rec, a field name field-name, and another expression new-value. It evaluates rec to a recV, then evaluates new-value, and then produces a recV containing all of rec’s fields, as well as a field named field-name with value new-value. If field-name is already on the given record then lookups on the new record should return new-value. extend should raise an exception if rec does not evaluate to a record value.

You should avoid writing test cases that return recVs. There are many different valid ways to represent records. For instance, a record with fields mapping a to 1 and b to 2 could be represented either as recV([fieldV("a", numV(1)), fieldV("b", numV(2))]) or as recV([fieldV("b", numV(2)), fieldV("a", numV(1))]), depending on the implementation. Your tests must be agnostic to their representation to allow both of these possibilities. You may instead test that a record has the right shape by calling lookup on it.

2 The New Grammar

Here are the extended data definitions:


==============================================================================

data Value:
  | numV(value :: Number)
  | strV(value :: String)
  | funV(params :: List<String>, body :: Expr, env :: Env)
  | recV(fields :: List<FieldV>)
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
    else if String(sexpr):
      idE(sexpr)
    end
  end
  convert(prog)
end

==============================================================================

(Again, parse is only shown for reference; you may use it if you want but don’t need to understand how it works.)

And the extended grammar:

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
 
<field> ::= (<id> <expr>)   // field name, followed by field value
 
where an id is not +, -, ++, ==, if, let, fun, assign, do, record,
lookup, or extend.
