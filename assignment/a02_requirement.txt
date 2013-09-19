1 Interpreter

You will write an interpreter for the Paret language, as described below. Your interpreter should have eager application semantics and use deferred substitution.

We have provided a function parse, which consumes an expression in the language’s concrete syntax (as returned by read-sexpr) and returns the abstract syntax representation of that expression. parse accepts expressions in the Grammar of the language.

To complete this assignment, you must implement the interp function. interp consumes an abstract syntax expression (as returned by the parse function) and returns a Paret-value. As with the tutorial you have already completed in Captain Teach, you will submit and review test cases for interp before writing the actual function. You should write your test cases in terms of the eval function, which is defined simply to call parse followed by interp. Your tests cases should fully cover the behavior of the Paret language. You may use the syntactic form eval("<some code>") raises "" to check that a program raises some sort of exception.

Parsing clarification: To parse a string str into an Expr, you must call parse(read-sexpr(str)), not just parse(str). Note that the eval function already does this for you, so you may write test cases like

*******************************************************************
eval('(++ "hello, " "world")') is C.strV("hello, world")
*******************************************************************



3 Grammar

The concrete syntax of the Paret language with these additional features can be captured with the following EBNF:

*******************************************************************
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
where an id is not +, -, ++, ==, if, let, or fun.
*******************************************************************

2 Features to Implement

2.1 Binary Operators

Paret includes binary addition (+) and subtraction (-), as well as string appending (++) and string equality testing (==). You may define these operations in terms of their counterparts in Pyret.

Evaluation should signal an error for non-numeric values passed to + and - operations, and for non-string values passed to ++ and == operations.

In place of having separate rules (and syntactic forms) for +, -, ++, and ==, we will define a single syntactic rule for all binary operators. parse converts these operators into the bop (for "binary operator") datatype variant (shown in the data definition below). Define a table that maps operator names (of type Operator) to actual functions (Pyret procedures) that perform the corresponding operation. Having a single rule like this, accompanied by a table, makes your language easier to extend: once you have modified your interpreter once to support binary operators, you won’t need to touch either one to add any number of new ones.

2.2 Conditionals

To save the trouble of having to add boolean values and operators over them, use the construct cif using the syntax described by the grammar below. cif behaves likes the if statement in the C programming language - the conditional counts as true whenever it is not zero. Note that cif has three branches:

    ==  A test expression

    ==  A "then" expression, which evaluates if the test expression 
        evaluates to any number other than zero

    ==  An "else" expression, which evaluates if the test expression
        evaluates to zero.

Evaluation should signal an error for non-numeric test values.

2.3 Multi-argument fun

Extend the fun language feature described in lecture so that functions can accept a list of zero or more arguments instead of just one. All arguments to the function must evaluate with the same deferred substitutions. An example of a multi-argument fun:

*******************************************************************
((fun (x y) (+ x y)) 2 3)
*******************************************************************

This evaluates to 5.
You should raise an exception when a function is called with the wrong number of arguments (this isn’t JavaScript, after all).

2.4 Let

The let expression should behave as described in the book, and should disallow recursive definitions. That is, in (let (<id> <expr>) <body>), <id> should be bound in <body> but not in <expr>.

4 Abstract Syntax

The abstract syntax for Paret is given below. These constructors will be available on the object C, so for instance you can write C.numV(3) to construct a numV. When writing cases statements, however, omit the C..

data Value:
  | numV(value :: Number)
  | strV(value :: String)
  | funV(params :: List<String>, body :: Expr, env :: Env)
end

data Env:
  | mt-env
  | an-env(name :: String, val :: Value, env :: Env)
end

data Expr:
  | id(name :: String)
  | num(value :: Number)
  | str(value :: String)
  | bop(op :: Operator, left :: Expr, right :: Expr)
  | cif(cond :: Expr, consq :: Expr, altern :: Expr)
  | let(name :: String, expr :: Expr, body :: Expr)
  | lam(params :: List<String>, body :: Expr)
  | app(func :: Expr, args :: List<Expr>)
end

data Operator:
  | plus
  | minus
  | append
  | str-eq
end
