TEST CASES

================================== 01 

fun eval(prog :: String) -> Value:
  interp(parse(read-sexpr(prog)))
end

fun interp(prog :: Expr) -> Value:
  interp-full(prog, mt-env, mt-store).val
end

fun interp-full(prog :: Expr, env :: Env, store :: Store) -> Result:

where:
  # With
   # Basic with usage
  eval('(let (stdlib (record (idf (fun (x) x)) (INT_MAX 64))) (with stdlib (idf INT_MAX)))') is numV(64)
   # Can't use with with non-record
  eval('(let (non-record 0) (with non-record (+ 0 0)))') raises ""
   # Limitations of with's scope
  eval('(do (with (record (x 0) (y 0)) (+ x y)) (+ x y))') raises ""
   # With shadows let
  eval('(let (shadow 0) (let (namespace (record (shadow 1))) (with namespace (+ shadow shadow))))') is numV(2)
   # Let shadows with
  eval('(with (record (x 0) (y 1)) (let (x 2) x))') is numV(2)
   # Shadow let binding with a record that has duplicate fields
  eval('(let (shadow 0) (let (namespace (record (shadow 8))) (do (assign namespace (extend namespace shadow 2)) (with namespace (+ shadow shadow)))))') is numV(4)
   # With shadows fun
  eval('((fun (x y) (with (record (x 2)) (+ x y))) 3 0)') is numV(2)
   # Fun shadows with
  eval('(with (record (x 2)) ((fun (x) x) 3))') is numV(3)
   # With shadows itself
  eval('(with (record (x 2)) (with (record (x 3)) x))') is numV(3)
   # Mutation might occur during record evaluation in a with clause
  eval('(let (mute (record (x 0))) (do (assign mute (record (x 1))) (lookup mute x)))') is numV(1)
   # Mutation might also occur in the evaluation of a with clauses's expression
  eval('(let (mute (fun () 0)) (do (with (record) (assign mute (fun () 1))) (mute)))') is numV(1)

  
  
  # OLD
  # Check binary operations
  eval('(+ 2 3)') is numV(5)
  eval('(- 3 2)') is numV(1)
  eval('(+ "x" "y")') raises '+ expects two numbers'
  eval('(- "x" "y")') raises '- expects two numbers'
  eval('(++ "x" "y")') is strV('xy')
  eval('(== "x" "y")') is numV(0)
  eval('(== "x" "x")') is numV(1)
  eval('(++ 0 0)') raises '++ expects two strings'
  eval('(== 0 0)') raises '== expects two strings'

  # Check if-else
  eval('(if 0 1 2)') is numV(2)
  eval('(if 1 1 2)') is numV(1)
  eval('(if (== "xx" "yy") (+ 1 2) (+ 2 3))') is numV(5)
  eval('(if "x" 1 2)') raises 'Condition must evaluate to a number'

  # Check fun
   # Function with no arguments
  eval('((fun () 2))') is numV(2)
  eval('((fun (y) y) 2)') is numV(2)
   # Correct number of arguments
  eval('((fun (x y) x) 0)') raises 'Too few arguments'
  eval('((fun (x) x) 0 0)') raises 'Too many arguments'
  eval('(let (z 5) ((fun (x) (+ x z)) 5))') is numV(10)

  # Check let
  eval('(let (x 5) (+ x x))') is numV(10)
  eval('(let (x "y") (++ x x))') is strV('yy')
   # No accessing variable outside of scope defined by let
  eval('(+ (let (x 5) x) x)') raises 'Unbound identifier: x'
   # Function has access to variable in same scope as function definition
  eval('(let (y 5) (let (f (fun (x) (+ x y))) (f 6)))') is numV(11)
   # Function composition
  eval('(let (f (fun (x) (+ x 1))) (let (g (fun (x) (+ (f x) 2))) (g 0)))') is numV(3)
   # Shadowing
  eval('(let (x 4) (let (f (fun (x) (+ x 1))) (+ x (f 2))))') is numV(7)
   # NO recursive function definitions via let
  eval('(let (f (fun (x) (f x))) (f 0))') raises "Unbound identifier: f"
  
  # Check assign
  eval('(let (x 1) (assign x 2))') is numV(2)
  eval('(let (x "abc") (assign x (- 2 1)))') is numV(1)
  eval('(assign x 0)') raises 'Unbound identifier: x'
   # Assign doesn't modify original shadowed variable
  eval('(let (x "tarski") (do (let (x 2) (assign x 1)) x))') is strV('tarski')

  # Check do
  eval('(let (x 0) (let (y 0) (do (assign x (+ 1 2)) (assign y (+ x 5)))))') is numV(8)
  eval('(let (f (fun (x y) (do (assign x 0) (assign y 0) (+ x y)))) (f 1 2))') is numV(0)
  eval('(++ (do (+ 0 0) (++ "a" "b")) "c")') is strV('abc')
  # More testing of check and do at the end

  # Records
   # Basic lookup
  eval('(lookup (record (x 2) (y 3)) y)') is numV(3)
   # Errors are handled
  eval('(lookup (record) dlo)') raises 'Field not found on record'
  eval('(lookup 0 x)') raises 'Cannot call lookup on non-record'
  eval('(extend 0 x 0)') raises 'Cannot call extend on non-record'
   # this should ideally be handled by the parser...
  eval('(lookup (record) 0)') raises ''
   # Nested records
  eval('(lookup (lookup (record (rec (record (rk 4)))) rec) rk)') is numV(4)
   # Basic extend
  eval('(lookup (extend (record) x "barwise") x)') is strV('barwise')
   # Add field with same name, then lookup
  eval('(lookup (extend (record (x "old")) x "new") x)') is strV('new')
   # Record and field name are the same
  eval('(let (x (record (x 0) (y 1))) (lookup x x))') is numV(0)
   # Update record value (kind of)
  eval('(let (rec (record (x 0))) (lookup (extend rec x (let (x (lookup rec x)) (assign x (+ x 1)))) x))') is numV(1)
   # Function with record as argument
  eval('(let (rec (record (zero 0) (one 1))) ((fun (rec) (lookup rec one)) rec))') is numV(1)

  # Check that store is passed along correctly
   # Binary operation, passed from left to right subexpression
  eval('(let (x 1) (+ (assign x (+ x 1)) x))') is numV(4)
   # Function application, passed from argument to argument
  eval('(let (x 0) (let (f (fun (x y) (+ x y))) (f (assign x 1) x)))') is numV(2)
   # If-else, passed from condition to branch
  eval('(let (mutt 0) (if (assign mutt 1) (+ mutt mutt) "asdf"))') is numV(2)
   # Mutation might occur within evaluation of assignment expression of assign
  eval('(let (x 2) (let (y 1) (do (assign x (do (assign y (+ y y)) (assign y (+ y y)))) (+ x y))))') is numV(8)
   # Mutation might occur during record definition...
  eval('(let (mutt "jockusch") (let (rec (record (x mutt) (y (assign mutt "soare")))) mutt))') is strV("soare")
   # ...but original record definition persists!
  eval('(let (mutt "jockusch") (let (rec (record (x mutt) (y (assign mutt "soare")))) (lookup rec x)))') is strV("jockusch")
   # Mutation might occur during record extension
  eval('(let (mutt "turing") (lookup (extend (record) x (assign mutt "church")) x))') is strV("church")

.................................. Behavior

The tests correctly reflect the desired behavior. The comments convince me that the 
implementation would be in good shape. 

.................................. Possible Inputs

The "with" test cases together with the previous test cases, from my point of view
has already covered all possible cases (at least in my case).


================================== 02

.................................. Behavior

line 120: there is an unbound identifier "x". It's neither in the current environment ([]),
nor declared in the "with" clause.

.................................. Possible Inputs

Remember to add cases that "with" can shadow itself, shadow "let", shadow parameters
in "fun" and etc.

Thirdly, arbitrarily added some mutation after "with" and inside the second expression in "with".

Lastly, added test cases where the first expression in "with" couldn't be evaluated to 
recV, namely namespace in the handout.

================================== 03

  # old basic interp tests, should all still work
  eval('(++ 5 "world")') raises ""
  eval('(++ "hello" 5)') raises ""
  eval('(++ 5 5)') raises ""
  eval('(== 5 "world")') raises ""
  eval('(== 5 5)') raises ""
  eval('(+ "hello" 5)') raises ""
  eval('(+ "hi" "there")') raises ""
  eval('(- "hello" 5)') raises ""
  eval('(- "hi" "there")') raises ""
  eval('(if "hello" 1 2)') raises ""
  eval('((fun (x y) (+ x y)) 2 3 4)') raises ""
  eval('((fun (x y) (+ x y)) 2)') raises ""
  eval('((fun (x y) (+ z (+ x y))) 2 3)') raises ""
  eval('((fun (x y) (let (z 3) (+ x y))) (2 + z) 3)') raises ""  
  eval('(let (x (fun (n) (if n (x (- n 1)) n))) (x 5))') raises ""
  eval('(++ "hello, " "world")') is strV("hello, world")
  eval('(++ "" "hey")') is strV("hey")
  eval('(++ "" "")') is strV("")
  eval('(== "hey" "no")') is numV(0)
  eval('(== "hey" "hey")') is numV(1)
  eval('(+ 5 7)') is numV(12)
  eval('(- 7 2)') is numV(5)
  eval('(if 1 1 0)') is numV(1)
  eval('(if 0 1 0)') is numV(0)
  eval('(if 18 1 0)') is numV(1)
  eval('((fun (x y) (- x y)) 2 3)') is numV(-1)
  eval('((fun (x y) (+ x y)) (+ 2 7) 3)') is numV(12)
  eval('(let (x 5) (+ x 4))') is numV(9)
  eval('(let (x (+ 4 5)) (+ x 2))') is numV(11)  
  # old state tests, should still work
  eval('(assign x 2)') raises ""
  eval('(do (let (x 3) x) (assign x 4) x)') raises ""
  eval('((fun (x) x) (do (assign x 5) x)') raises ""
  eval('(let (x 1) (do (let (y 3) y) (assign x y) x))') raises ""
  eval('(let (x 1) (do (assign x (+ 4 "hi")) x))') raises ""
  eval('(+ (let (x 5) x) (do (assign x 2) x))') raises ""
  eval('(let (x 1) (assign x 2))') is numV(2)
  eval('(let (x 1) (do (assign x 2) x))') is numV(2)
  eval('(let (x 1) (do (assign x 3) (assign x 4) x))') is numV(4)
  eval('(let (x 1) (do (assign x 2) (let (x 3) x) x))') is numV(2)
  eval('(let (x 1) (do (assign x (+ x x)) x))') is numV(2)
  eval('(let (x 4) (let (y 5) (let (x 6) (do (assign x (+ x 1)) (assign y (+ y 2)) (+ y x)))))') is numV(14) 
  eval('(let (x 4) (+ (let (x 20) (do (assign x 30) x)) x))') is numV(34)
  eval('(let (z 5) (do ((fun (x) (do (assign x 99) x)) z) z))') is numV(5)
  eval('(let (z 5) (do ((fun (z) (do (assign z 99) z)) z) z))') is numV(5)
  eval('(let (x 1) (do (assign x (+ x 1)) (assign x (+ x 1)) x))') is numV(3)
  eval('(let (x 1) (let (y 1) (do (do (assign x 2) (assign y 2)) (+ x y))))') is numV(4)
  eval('(let (x 5) (do ((fun () (assign x 10))) x))') is numV(10)
  eval('(let (x 5) (let (y 7) (do (assign x (do (assign y 10) (+ 5 y))) (+ y x))))') is numV(25)
  eval('(let (x 0) (if (assign x 1) x -5))') is numV(1)
  eval('(let (x 3) (let (y 0) ((fun (a b) (+ a b)) (do (assign y 5) (assign x 3) x) y)))') is numV(8)
  # old tests for record
  eval('(lookup (record (y 1)) x)') raises ""
  eval('(lookup 5 x)') raises ""
  eval('(let (z 5) (lookup z x))') raises ""
  eval('(extend "bonjour" x 10)') raises ""
  eval('(let (z 5) (extend z x 10))') raises ""
  eval('(lookup (record (x 1)) x)') is numV(1) 
  eval('(lookup (record (x 1) (y 1)) y)') is numV(1)
  eval('(lookup (record (x (+ 5 6))) x)') is numV(11)
  eval('(lookup (let (x 5) (record (y (+ 5 x)))) y)') is numV(10)
  eval('(let (x (record (y 5))) (lookup x y))') is numV(5)
  eval('(lookup (lookup (record (x (record (y 5)))) x) y)') is numV(5)
  eval('(lookup (lookup (record (x (record (x 5)))) x) x)') is numV(5)
  eval('(lookup (record (x (let (z 5) (do (assign z 10) z)))) x)') is numV(10)
  eval('(lookup (extend (record (x 1)) y 2) y)') is numV(2)
  eval('(lookup (extend (record (x 1)) x 2) x)') is numV(2)
  eval('(lookup (extend (extend (record (x 1)) y 3) z 4) z)') is numV(4)
  eval('(let (x (record (z 5))) (lookup (extend x z (+ 5 (lookup x z))) z))') is numV(10)
  eval('(lookup (let (x 10) (record (a (assign x 5)) (b x))) b)') is numV(5)
  
  # new tests for WITH
  eval('(with 5 5)') raises "" # when the record is a different Value
  eval('(with (+ 5 5) 5)') raises "" # when the record field evaluates to a non-record Value
  eval('(with (record (x 5)) x)') is numV(5) # basic use of with
  eval('(with (record (x 5) (y 10)) (+ x y))') is numV(15) # multiple entries in the record
  eval('(let (x (record (y 5))) (with x y))') is numV(5) # having to evaluate the record
  eval('(let (x (record (x 5))) (with x x))') is numV(5) # a record entry shadowing the record itself
  eval('(let (y 5) (with (record (y 10)) y))')  is numV(10) # a record entry shadowing an exterior identifier
  eval('(with (record (x (record (z 10)))) (with x z))') is numV(10) # a with within a with
  eval('(with (record (x 10)) (do (assign x 5) x))') is numV(5) # mutating a record's with value
  eval('(let (x (record (z 10))) (with x (+ z (lookup x z))))') is numV(20) # having the record interacting with one of its fields in the wild
  eval('
    (let (x 5) 
         (with (record (a (assign x 10))) x))') is numV(10) # threading the evaluation of the record into the evaluation of the body 

.................................. Behavior

The tests correctly reflect the desired behavior. The comments convince me that the 
implementation would be in good shape. 

.................................. Possible Inputs

The "with" test cases together with the previous test cases, from my point of view
has already covered all possible cases (at least in my case).


