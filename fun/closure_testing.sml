use "currying.sml";

val test_only_capitals = only_capitals ["abc", "Abc", "AAA", "OK"] = ["Abc", "AAA", "OK"]

val test_longest_string1 = longest_string1 ["aeiou", "okay"] = "aeiou"

val test_longest_string1_tie = longest_string1 ["aeiou", "ouiea"] = "aeiou"

val test_longest_string2 = longest_string2 ["aeiou", "ouiea"] = "ouiea"

val test_longest_string3 = longest_string3 ["aeiou", "ouiea"] = "aeiou"

val test_longest_string4 = longest_string4 ["aeiou", "ouiea"] = "ouiea"

val test_longest_capitalized = longest_capitalized ["abc", "Abc", "AAA", "OK"] = "Abc"

val test_rev_string = rev_string "aeiou" = "uoiea"

val test_rev_string_empty = rev_string "" = ""

val test_first_answer = first_answer (fn x => if x > 3 then SOME x else NONE) [0, 2, 1, 4, 5] = 4

fun fun_first_answer_nothing () =
    first_answer (fn x => if x > 3 then SOME x else NONE) [1, 2]

val test_first_answer_nothing = (fun_first_answer_nothing () handle e => 0) = 0

val test_all_answers = all_answers (fn x => if x > 3 then SOME [x] else NONE) [7, 4, 5] = SOME [7, 4, 5]

val test_all_answer_nothing = all_answers (fn x => if x > 3 then SOME [x] else NONE) [3, 0] = NONE

fun fun_count_wildcard counter =
    let val p = Wildcard
    in
	counter p
    end

fun fun_count_variable counter =
    let val p = Variable "3"
    in
	counter p
    end

fun fun_count_tuple counter =
    let val p = TupleP [Variable "3", Wildcard, Wildcard]
    in
	counter p
    end

fun fun_count_constructor counter =
    let val inner_p = TupleP [Variable "3", Wildcard, Wildcard]
	val p = ConstructorP ("constr", inner_p)
    in
	counter p
    end

val test_count_wildcards_wildcard = fun_count_wildcard count_wildcards = 1
val test_count_wildcards_variable = fun_count_variable count_wildcards = 0
val test_count_wildcards_tuple = fun_count_tuple count_wildcards = 2
val test_count_wildcards_constructor = fun_count_constructor count_wildcards = 2

val test_count_wild_and_variable_wildcard = fun_count_wildcard count_wild_and_variable_lengths = 1
val test_count_wild_and_variable_variable = fun_count_variable count_wild_and_variable_lengths = 1
val test_count_wild_and_variable_tuple = fun_count_tuple count_wild_and_variable_lengths = 3
val test_count_wild_and_variable_constructor = fun_count_constructor count_wild_and_variable_lengths = 3

val test_count_some_var_wildcard = count_some_var ("str", Wildcard) = 0
val test_count_some_var_variable = count_some_var ("str", Variable "str") = 1
val test_count_some_var_tuple = count_some_var ("str",
						TupleP [Variable "3",
							Wildcard,
							Wildcard,
							Variable "str"]) = 1
val test_count_some_var_constructor = count_some_var ("str",
						      ConstructorP ("str", TupleP [Variable "str"])) = 1

val test_check_pat = check_pat (ConstructorP ("3", TupleP [Variable "3", Wildcard, Variable "hi"])) = true
val test_check_pat_duplicate = check_pat (ConstructorP ("3", TupleP [Variable "3", Wildcard, Variable "3"])) = false

val valuUnit = Unit
val valuConst = Const 3
val valuTuple = Tuple [Const 3, Unit, Tuple [Const 4, Constructor ("Constructor", Const 7)]]
val valuConstructor = Constructor ("Single constructor", Const 9)

val test_match_unit_variable = match (Unit, Variable "hi") = SOME [("hi", Unit)]
val test_match_unit = match (Unit, UnitP) = SOME []
val test_match_const_false = match (valuConst, ConstP 9) = NONE
val test_match_const_true = match (valuConst, ConstP 3) = SOME []
val test_match_constructor_true = match (valuConstructor, ConstructorP ("Single constructor", ConstP 9)) = SOME []
val test_match_constructor_false = match (valuConstructor, ConstructorP ("Single constructor", ConstP 3)) = NONE
val test_match_tuple_true = match (valuTuple, TupleP [ConstP 3, UnitP, TupleP [ConstP 4, ConstructorP ("Constructor", ConstP 7)]]) = SOME []

val test_first_match = ((first_match valuConst) [UnitP, ConstP 3, UnitP, TupleP [ConstP 4, ConstructorP ("Constructor", ConstP 7)]]) = SOME []
