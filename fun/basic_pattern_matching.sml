(* Week 2:

      This problem For example, Fredrick William Smith could also be Fred William Smith or
      Freddie William Smith. Only part (d) is

      (a) Write a function all_except_option, which takes a string and a string list. Return
          NONE if the string is not in the list, else return SOME lst where lst is identical
          to the argument list except the string is not in it. You may assume the string is
          in the list at most once. Use same_string, provided to you, to compare strings.
          Sample solution is around 8 lines.

      (b) Write a function get_substitutions1, which takes a string list list (a list of list
          of strings, the substitutions) and a string s and returns a string list. The result
          has all the strings that are in some list in substitutions that also has s, but s
          itself should not be in the result.

          Example:

          get_substitutions1(
                 [["Fred","Fredrick"],["Elizabeth","Betty"],["Freddie","Fred","F"]], "Fred")

          (* answer: ["Fredrick","Freddie","F"] *)

          Assume each list in substitutions has no repeats. The result will have repeats if s
          and another string are both in more than one list in substitutions.

          Example:

          get_substitutions1(
                 [["Fred","Fredrick"],["Jeff","Jeffrey"],["Geoff","Jeff","Jeffrey"]], "Jeff")

          (* answer: ["Jeffrey","Geoff","Jeffrey"] *)

          Use part (a) and ML’s list-append (@) but no other helper functions. Sample solution
          is around 6 lines.

      (c) Write a function get_substitutions2, which is like get_substitutions1 except it uses
          a tail-recursive local helper function.

      (d) Write a function similar_names, which takes a string list list of substitutions (as
          in parts (b) and (c)) and a full name of type

          {first:string, middle:string, last:string}

          and returns a list of full names (type 

          {first:string, middle:string, last:string} list

          ). The result is all the full names you can produce by substituting for the ﬁrst
          name (and only the ﬁrst name) using substitutions and parts (b) or (c).

          The answer should begin with the original name (then have 0 or more other names).

          Example:

          similar_names([["Fred","Fredrick"],["Elizabeth","Betty"],["Freddie","Fred","F"]],

          {first="Fred", middle="W", last="Smith"})
                                   
          (* answer:

          [{first="Fred", last="Smith", middle="W"},
          {first="Fredrick", last="Smith", middle="W"},
          {first="Freddie", last="Smith", middle="W"},
          {first="F", last="Smith", middle="W"}]

          *)
*)

fun same_string (s1 : string, s2 : string) =
    s1 = s2

fun all_except_option (str, str_list) =
    let fun aux (first_half, sec_half) =
            case sec_half of
                [] => NONE
              | head :: rest => if same_string (str, head) then
                                    SOME (first_half @ rest)
                                else
                                    aux (first_half @ [head], rest)
    in
        aux ([], str_list)
    end

fun get_substitutions (subs, s) =
    let fun aux (pre, subs) =
            case subs of
                [] => pre
              | head_list :: rest => case all_except_option (s, head_list) of
                                         NONE => aux (pre, rest)
                                       | SOME c => aux (pre @ c, rest)
    in
        aux ([], subs)
    end

fun similar_names (subs, full_name) =
    let fun aux (pre, similars, middle, last) =
            case similars of
                [] => pre
              | head :: tail => aux (pre @ [{ first = head, middle = middle, last = last }],
                                     tail, middle, last)
    in
        case full_name of
            { first, middle, last } =>
            full_name :: aux ([], get_substitutions (subs, first), middle, last)
    end
