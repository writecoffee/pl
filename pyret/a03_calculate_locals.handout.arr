Calculating Locals

1 Autocomplete

One helpful feature that IDEs (Integrated Development Environments) often provide is the ability to autocomplete an identifier as it is being typed, or, similarly, to underline unbound identifiers with a "red squiggly".

This is in general a hard problem – depending, for instance, on what modules were imported. You will solve a simplified version of this problem. You will write a function that takes an expression with a "hole" in it and returns the set of identifiers that can occur at that position.

2 Your Task

Paret’s grammar has been extended with a new type of expression called a "hole". It is written as @ in the concrete syntax, and is constructed with hole in the abstract syntax. Your task is to write a functioncalculate-locals to compute the set of all possible identifiers that may be placed at this point in the expression - 

*** that is, the set of all identifiers which are in scope at the hole. ***

You may assume that an expression has exactly one hole, and should avoid writing test cases that include no holes or more than one hole.

Write your test cases in terms of parse-and-calculate-locals – it will make them easier to read.

calculate-locals must return a Set of strings. Sets can be constructed from a list using the function set, and extended using the method add. See the Pyret documentation for their full interface.

For reference, here is the extended grammar:

<expr> ::= <num>
         | <string>
         | <id>
         | (+ <expr> <expr>)   // addition
         | (- <expr> <expr>)   // subtraction
         | (++ <expr> <expr>)  // string append
         | (== <expr> <expr>)  // string equality
         | (if <expr> <expr> <expr>)
         | (let (<id> <expr>) <expr>)
         | (fun (<id> ...) <expr>)
         | (<expr> <expr> ...) // application
         | @                 // a "hole"

where an id is not +, -, ++, ==, if, let, or fun.

and the extended abstract syntax:

data Expr:
  | id(name :: String)
  | num(value :: Number)
  | str(value :: String)
  | bop(op :: Operator, left :: Expr, right :: Expr)
  | cif(cond :: Expr, consq :: Expr, altern :: Expr)
  | let(name :: String, expr :: Expr, body :: Expr)
  | lam(params :: List<String>, body :: Expr)
  | app(func :: Expr, args :: List<Expr>)
 
  | hole
end
 
data Operator:
  | plus
  | minus
  | append
  | str-eq
end

