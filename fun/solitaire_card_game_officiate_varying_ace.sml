(* Week 2:

      Write score_challenge and officiate_challenge to be like their non-challenge
      counterparts except each ace can have a value of 1 or 11 and score_challenge
      should always return the least (i.e., best) possible score.
*)
fun officiate_challenge(card_list, move_list, goal) =
    let fun aux(pre_sum, card_list, move_list, held_cards) =
            case (card_list, move_list, held_cards) of
                (_, [], _) => 
                score_challenge(held_cards, goal)
              | ([], _, _) =>
                score_challenge(held_cards, goal)
              | (cs, Discard(c) :: rest_moves, helds) =>
                aux(pre_sum, cs, rest_moves, remove_card(helds, c, IllegalMove))
              | ((suit, Ace) :: cs, Draw :: rest_moves, helds) =>
                let val tsum1 = pre_sum + 1
                    val tsum11 = pre_sum + 11
                    val new_helds = (suit, Ace) :: held_cards
                in
                    if tsum1 > goal then
                        score_challenge(new_helds, goal)
                    else if tsum11 > goal then
                        Int.min(score_challenge(new_helds, goal),
                                aux(tsum1, cs, rest_moves, new_helds))
                    else
                        Int.min(aux(tsum1, cs, rest_moves, new_helds),
                                aux(tsum11, cs, rest_moves, new_helds))
                end
              | (c :: cs, Draw :: rest_moves, helds) =>
                let val new_sum = card_value(c) + pre_sum
                in
                    if new_sum > goal then
                        score_challenge(c :: helds, goal)
                    else
                        aux(new_sum, cs, rest_moves, c :: helds)
                end
    in
        aux(0, card_list, move_list, [])
    end

