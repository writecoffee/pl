Implementing an Interpreter - Lifting Locals

In this assignment, you will restructure Paret to have block-structured scoping, as in many scripting languages. You may refer to the new language as Paret-with-blocks.

1 Extensions

A block-structured language makes a distinction between expressions and statements. Roughly speaking, a block is a sequence of statements, each of which do something, whereas an expression computes a value.

More precisely, in Paret-with-blocks, a block consists of a sequence of stmts. Each stmt is a defvar statement, an assignment, or an expr.

1.1 Null

null is a new kind of value. It isn’t very useful. In particular, null is not a number, so any operation that expects a number (like addition, or the condition in an if) but is given null instead fails in Paret-with-blocks.

The null expression (represented as nullE in the abstract syntax) simply evaluates to the null value.

1.2 Defvar

defvar statements are similar to the let expressions they replace. However, they do not contain a body (just an identifier and an expression to bind it to), and the identifier they bind is in scope in the entire surrounding block. If the identifier is referenced in the block before the defvar statement defining it is evaluated, that identifier evaluates to null. And if the identifier is referenced after the defvar statement, it evaluates to the value that the statement binds it to. An identifier occuring in its own binding (like (defvar x x)) evaluates to null.

This can be accomplished by lifting identifiers defined by defvar statements up to the top of their block and binding them to null, and then changing the defvar statements into assignments. Of course, if you wish to use a different implementation strategy you are free to do so.

1.3 Assign

assign statements behave the same as they did before, though they are now statements instead of expressions. As before, assign can modify the arguments bound to function parameters.

1.4 Blocks

When evaluated, blocks evaluate their statements in order, and produce the value of their last statement. If they end in a defvar statement or an assign statement, they produce the value being bound or assigned, respectively.

If a block contains more than one defvar binding the same identifier, your interpreter should raise an exception when evaluating that block. It is OK, however, for a nested block to use the same identifier as an outer block, and this should not on its own raise an exception.

2 The New Grammar

 
<prog> ::= <stmt> <stmt> ...  // called a 'block' in the abstract syntax
 
<stmt> ::= (defvar <id> <expr>)
         | (assign <id> <expr>)
         | <expr>
 
<expr> ::= <num>
         | <string>  // strings, surrounded by double quotes ""
         | <id>
         | (+ <expr> <expr>)   // addition
         | (- <expr> <expr>)   // subtraction
         | (++ <expr> <expr>)  // string append
         | (== <expr> <expr>)  // string equality
         | (if <expr> <expr> <expr>)
         | (fun (<id> ...) <stmt> <stmt> ...) // one or more stmts
         | (<expr> <expr> ...) // application
         | (record <field> ...) // each field must have a different name
         | (lookup <expr> <id>)
         | (extend <expr> <id> <expr>)
         | null
 
<field> ::= (<id> <expr>)   // field name, followed by field value
2.1 Statements vs. Expressions

Notice that in the grammar, expressions may be used in place of statements, but not vice-versa. Thus a program like (+ (assign x 1) 2) is now syntactically invalid, i.e. it does not conform to the grammar. You do not need to check that your input program conforms to the grammar, and should not write test cases of programs that do not conform to the grammar.

There are other changes to the grammar as well (such as the removal of let, do, and with). When writing your test cases, carefully ensure that the programs you write conform to the new grammar.

Your program as a whole is now a list of statements, instead of an expression. Thus "1 2 3" is a valid Paret-with-blocks program that evaluates to 3. And
(defvar y (fun () x))
(defvar x 1)
(y)
is a valid program that evalutes to 1.
Function bodies are also now blocks, so that (fun (x) (defvar y 1) y) is a valid function. This begs the question of how function parameters, defvars, and assignments within the function body should interact. If there is a defvar in a function body for an identifier which is also a function parameter, the defvar should introduce a new binding to the environment that shadows the function parameter.

The new data definitions (i.e. abstract syntax) are below. To parse a Paret-with-blocks expression, call parse(read-sexpr-list(’some code’)). (This change comes about because ’1 2 3’ is now a valid program, but is really a sequence of s-expressions, rather than a single s-expression.) As always, eval is defined for you, and parses its input for you.

