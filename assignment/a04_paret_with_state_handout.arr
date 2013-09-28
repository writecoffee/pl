Implementing an Interpreter - Adding State

In this assignment, you will add state to the Paret language by allowing variable mutation. You may refer to the new language as Paret-with-state.

An Important Change: We are changing the way you construct Exprs in this assignment. There are three changes.

First, all of the names are available directly in the environment, instead of being on an object called C. So you should write strV("hi") instead of C.strV("hi"), and Expr instead of C.Expr.

Second, the constructors for Expr have been renamed to have E at the end, for instance, letE instead of let. You can see the change in the definitions below.

Third, in previous assignments the parser was lenient and let you write "(let x 1 x)" instead of "(let (x 1) x)" even though this technically was forbidden by the grammar. You must now strictly obey the grammar and write "(let (x 1) x)".

For instance, you should now write:

eval('(let (x 3) (+ x 1))') is numV(4)

Make sure you take this into account when writing your test cases for this assignment. If any of your test cases use C. or say "(let x 1 ...)", they will fail when we run them. In particular, if you copy/paste test cases from previous assignments, you must fix them to work with these changes.

1 The Extended Language

The grammar (and the Expr data type) has been extended with two new forms:

1.1 assign

assign takes an identifier and an expression, evaluates the expression to a value, and assigns that value to the identifier by modifying its location in the store. The result of an assign expression is the new value of the identifier. For instance, the Paret-with-state program

(let (x 1) (assign x 2))

should evaluate to 2.

If the identifier in an assign expression is not in scope, you should raise an exception – it doesn’t make sense to change the value of an identifier not bound in the environment!

1.2 do

do takes a sequence of expressions and evaluates them in order. It returns the value of the last expression in the sequence.

2 Implementing the Interpeter

Your task is to add state to Paret. You should closely follow the store-passing style we studied in class and that is presented in the book. We will define the store slightly differently than it is defined in the book (this version will be better type-checked):

###############################################################
data Store:
  | mt-store
  | a-store(loc :: String, val :: Value, store :: Store)
end
###############################################################

And the signature for the interpreter itself has two parts:

###############################################################
fun interp-full(
    prog :: Expr,
    env :: Env,
    store :: Store
  ) -> Result:
  # your code here...
end
 
data Result:
  | result(val :: Value, store :: Store)
end
############################## END ###########################


That is, the interpreter, defined by interp will evaluate Exprs into Values. However, we the function interp-full will do the heavy lifting, by also takeing an environment and a store, and producing a value and an updated store. This is the signature that’s needed to make store passing style work, and will be necessary for implementing Paret-with-state’s stateful assign operation.

You will need to generate store locations, and can use the built-in gensym function to do so. See the miscellaneous functions list in the Pyret documentation.

Note that this interpreter is an extension of the previous one (interp-basic). As such, you may feel free to copy your code from the previous interpreter while implementing the new one.

Here are the extended data definitions:


###############################################################
 
data Value:
  | numV(value :: Number)
  | strV(value :: String)
  | funV(params :: List<String>, body :: Expr, env :: Env)
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
end
 
data Operator:
  | plus
  | minus
  | append
  | str-eq
end
 
fun parse(prog) -> Expr:
  doc: "Parse a string matching Paret's concrete syntax into an Expr."
 
  fun check-params(params :: List<String>) -> List<String>:
    doc: "Ensure that a function has no duplicate parameter names."
    for each(param from params):
      when params.filter(fun(x): x == param end).length() > 1:
        raise("parse: function has duplicate parameter " + param)
      end
    end
    params
  end
 
  fun convert(sexpr):
    doc: "Convert an s-expression into an Expr."
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
      else if head == "assign":
        assignE(sexpr.get(1), convert(sexpr.get(2)))
      else if head == "do":
        when is-empty(sexpr.rest):
          raise("Paret: do blocks cannot be empty")
        end
        doE(map(convert, sexpr.rest))
      else if head == "fun":
        lamE(check-params(sexpr.get(1)), convert(sexpr.get(2)))
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

############################## END ###########################

We have also included a ’parse’ function for you. It is shown for reference, though you do not need to understand how it works.

And here is the extended grammar:

###############################################################

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

############################## END ###########################
 
where an id is not +, -, ++, ==, if, let, fun, assign, or do.
