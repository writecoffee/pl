(* Week 2:

      Write careful_player, which takes a card-list and a goal and returns a move-list
      such that calling officiate with the card-list, the goal, and the move-list has
      this behavior:

      - The value of the held cards never exceeds the goal.
      - A card is drawn whenever the goal is more than 10 greater than the value of the
        held cards.
      - If a score of 0 is reached, there must be no more moves.
      - If it is possible to discard one card, then draw one card to produce a score of
        0, then this must be done. (Note careful_player will have to look ahead to the
        next card, which in many card games is considered "cheating.")
*)
fun careful_player(cs, goal) =
    let fun discard(last, pre_held, gap) =
            (* This is a greedy algorithm for picking a card to discard when the current
               total value goes over 10 + goal. Because we have applied insertion sort
               every time we draw a card from the pool, it's straightforward that we can
               discard a card whose value is >= 10 *)
            case pre_held of
                [] => raise IllegalMove
              | (head :: []) => (head, last)
              | (head :: next :: rest) => if card_value(head) < gap then
                                              discard(last @ [head], next :: rest, gap)
                                          else
                                              (head, last @ [next] @ rest)
        fun insert(last, new_card, held_cards) =
            case held_cards of
                [] => last @ [new_card]
              | head :: rest => if card_value(head) >= card_value(new_card) then
                                    last @ [new_card] @ held_cards
                                else
                                    insert(last @ [head], new_card, rest)                                      
        fun aux(cs, pre_held, pre_moves, value) =
            (* If the goal is set to be too small such that applying this "conservative"
               mindset will lead to empty card held for this player *)
            if value = goal then
                pre_moves
            else
                case (cs, pre_held) of
                    ([], _) => pre_moves
                  | (head_card :: rest_cards, []) =>
                    if value + card_value(head_card) <= goal then
                        aux(cs, insert([], head_card, pre_held), pre_moves @ [Draw],
                            card_value(head_card) + value)
                    else
                        []
                  | (head_card :: rest_cards, head_held :: rest_helds) =>
                    if value + card_value(head_card) <= goal then
                        aux(cs, insert([], head_card, pre_held), pre_moves @ [Draw],
                            card_value(head_card) + value)
                    else
                        let val (discarded, non_discarded) = 
                                discard([], pre_held, value + card_value(head_card) - goal)
                        in
                            aux(cs, non_discarded, pre_moves @ [Discard(discarded)],
                                value - card_value(discarded))
                        end
    in
        aux(cs, [], [], 0)
    end
