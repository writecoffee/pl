use "basic_pattern_matching.sml";
use "solitaire_card_game.sml";
use "testing.sml";
open SmlTests;

test ("all_except_option: Remove 'abc' from input list.",
      assert_equals_string_list_option (SOME (["add", "ook"]),
					all_except_option ("abc", ["abc", "add", "ook"])));

test ("all_except_option: No target found in input list.",
      assert_equals_string_list_option (NONE,
					all_except_option ("abc", ["add", "ook"])));

test ("all_excpet_option: Empty target list.",
      assert_equals_string_list_option (NONE,
					all_except_option ("abc", [])));

test ("all_except_option: Remove 'abc' from the end of the input list.",
      assert_equals_string_list_option (SOME (["bbc", "add"]),
					all_except_option ("abc", ["bbc", "add", "abc"])));

test ("get_substitutions: Yield a resulting list without 'Fred'.",
      assert_equals_string_list (["Fredrick", "Freddie", "F"],
				 get_substitutions ([["Fred", "Fredrick"],
						     ["Elizabeth", "Betty"],
						     ["Freddie", "Fred", "F"]], "Fred")));

test ("get_substitutions: Yield a resulting list without 'Jeff'.",
      assert_equals_string_list (["Jeffrey", "Geoff", "Jeffrey"],
				 get_substitutions ([["Fred", "Fredrick"],
						     ["Jeff", "Jeffrey"],
						     ["Geoff", "Jeff", "Jeffrey"]], "Jeff")));

test ("get_substitutions: Yield an empty result list.",
      assert_equals_string_list ([],
				 get_substitutions ([["Fred", "Fredrick"],
						     ["Elizabeth", "Betty"],
						     ["Freddie", "Fred", "F"]], "Hello")));

run();

val test11 = similar_names ([["Fred", "Fredrick"],
			     ["Elizabeth", "Betty"],
			     ["Freddie", "Fred", "F"]],
			    { first="Fred", middle="W", last="Smith" })
	     = [{ first="Fred", last="Smith", middle="W" },
		{ first="Fredrick", last="Smith", middle="W" },
		{ first="Freddie", last="Smith", middle="W" },
		{ first="F", last="Smith", middle="W" }]

val test12 = remove_card ([(Clubs, Ace), (Diamonds, Num (3))], (Diamonds, Num (3)), IllegalMove)
			 = [(Clubs, Ace)]

fun officiate_test1 () = (* correct behavior: raise IllegalMove *)
    let val cards = [(Clubs,Jack),(Spades,Num(8))]
	val moves = [Draw,Discard(Hearts,Jack)]
    in
	officiate(cards,moves,42)
    end

val test13 = (officiate_test1 () handle e => ~1) = ~1

fun officiate_test2 () = (* correct behavior: return 3 *)
    let val cards = [(Clubs,Ace),(Spades,Ace),(Clubs,Ace),(Spades,Ace)]
	val moves = [Draw,Draw,Draw,Draw,Draw]
    in
	officiate(cards, moves, 42)
    end

val test14 = officiate_test2 () = 3

fun officiate_test3 () = (* correct behavior: return 6 *)
    (* two different colors *)
    let val cards = [(Clubs, Ace), (Diamonds, Ace), (Clubs, Ace), (Spades, Ace)]
	val moves = [Draw, Draw, Draw, Draw]
    in
	officiate (cards, moves, 50)
    end

val test15 = officiate_test3 () = 6

fun officiate_test3' () = (* correct behavior: return 12 *)
    (* two different colors *)
    let val cards = [(Clubs, Ace), (Diamonds, Ace), (Clubs, Ace), (Spades, Ace), (Clubs, Num 10)]
	val moves = [Draw, Draw, Draw, Draw, Draw]
    in
	officiate (cards, moves, 50)
    end

val test16 = officiate_test3' () = 12

fun officiate_test4 () = (* correct behavior: return 8 *)
    (* two different colors *)
    let val cards = [(Clubs,Ace),(Diamonds,Ace),(Clubs,Ace),(Spades,Ace),(Clubs,Num 10)]
	val moves = [Draw,Draw,Discard (Diamonds,Ace),Draw,Draw]
    in
	officiate (cards,moves,50)
    end

val test17 = officiate_test4 () = 8

fun officiate_test5 () = (* correct behavior: return 17 *)
    (* two different colors *)
    let val cards = [(Clubs,Ace),(Diamonds,Ace),(Clubs,Ace),(Spades,Ace),(Clubs,Num 10)]
	val moves = [Draw,Draw,Discard (Clubs,Ace),Draw,Draw]
    in
	officiate (cards, moves, 50)
    end

val test18 = officiate_test5 () = 17

