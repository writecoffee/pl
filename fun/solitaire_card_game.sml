(* Week 2:

      This problem involves a solitaire card game invented just for this question.
      You will write a program that tracks the progress of a game; writing a game
      player is a challenge problem. You can do parts (a)–(e) before understanding
      the game if you wish.

      A game is played with a card-list and a goal. The player has a list of
      held-cards, initially empty. The player makes a move by either drawing, which
      means removing the first card in the card-list from the card-list and adding
      it to the held-cards, or discarding, which means choosing one of the held-cards
      to remove. The game ends either when the player chooses to make no more moves
      or when the sum of the values of the held-cards is greater than the goal.

      The objective is to end the game with a low score (0 is best). Scoring works
      as follows: Let sum be the sum of the values of the held-cards. If sum is
      greater than goal, the preliminary score is three times sum − goal, else the
      preliminary score is goal − sum. The score is the preliminary score unless all
      the held-cards are the same color, in which case the score is the preliminary
      score divided by 2 (and rounded down as usual with integer division; use ML’s
      div operator).
*)

datatype suit = Clubs | Diamonds | Hearts | Spades
datatype rank = Jack | Queen | King | Ace | Num of int 
type card = suit * rank

datatype color = Red | Black
datatype move = Discard of card | Draw 

exception IllegalMove

fun card_color (c) =
    case c of (Spades, _) => Black
	    | (Clubs, _) => Black
	    | (Hearts, _) => Red
	    | (Diamonds, _) => Red

fun card_value (c) =
    case c of (_, Ace) => 11
	    | (_, Num (num)) => num
	    | _ => 10

fun remove_card (cs, c : (suit * rank), e) =
    let fun aux (pre, cs) =
	    case cs of
		[] => raise e
	     | head :: tail => if head = c then
				   pre @ tail
			       else
				   aux (pre @ [head], tail)
    in
	aux ([], cs)
    end

fun all_same_color (cs) =
    case cs of
	[] => true
      | _ :: [] => true
      | first :: second :: rest => card_color (first) = card_color (second)
				   andalso all_same_color (second :: rest)

fun sum_cards (cs) =
    let fun aux (pre, cs) =
	    case cs of
		[] => pre
	     | head :: tail => aux (pre + card_value (head), tail)
    in
	aux (0, cs)
    end

fun score (cs, goal) =
    let val tsum = sum_cards (cs)
	val preliminary = if tsum > goal then (tsum - goal) * 3 else goal - tsum
    in 
	if all_same_color (cs) then
	    preliminary div 2
	else
	    preliminary
    end

fun officiate (card_list, move_list, goal) =
    let fun aux (card_list, move_list, held_cards) =
	    case (card_list, move_list, held_cards) of
		(_, [], _) => score (held_cards, goal)
	     | ([], _, _) => score (held_cards, goal)
	     | (cs, Discard (c) :: rest_moves, helds) =>
	       aux (cs, rest_moves, remove_card (helds, c, IllegalMove))
	     | (c :: cs, Draw :: rest_moves, helds) =>
	       let val new_helds = c :: helds
		   val tsum = sum_cards (new_helds)
	       in
		   if tsum > goal then
		       score (new_helds, goal)
		   else
		       aux (cs, rest_moves, new_helds)
	       end
    in
	aux (card_list, move_list, [])
    end

fun retrieve_suit (card) =
    case card of
	(Diamonds, _) => Diamonds
      | (Spades, _) => Spades
      | (Clubs, _) => Clubs
      | (Hearts, _) => Hearts

fun score_challenge (cs, goal) =
    let fun aux (pre, cs) =
	    case cs of
		[] => score (pre, goal)
              | first :: rest =>
		if card_value (first) = 11 then
                    Int.min (aux (first :: pre, rest),
                             aux ((retrieve_suit (first), Num (1)) :: pre, rest))
                else
                    aux (first :: pre, rest)
    in
        aux ([], cs)
    end
