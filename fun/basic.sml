(* Week 1:

   1. Write a function is_older that takes two dates and evaluates to true
      or false. It evaluates to true if the ﬁrst argument is a date that comes
      before the second argument. (If the two dates are the same, the result is
      false.)
*)
fun is_older(d1 : int * int * int, d2 : int * int * int) =
    let val y1=(#1 d1) val m1=(#2 d1) val day1=(#3 d1)
        val y2=(#1 d2) val m2=(#2 d2) val day2=(#3 d2)
    in
        y1 < y2 orelse (y1 = y2 andalso m1 < m2) orelse (y1 = y2 andalso m1 = m2 andalso day1 < day2)
    end

(* 2. Write a function number_in_month that takes a list of dates and a month
      (i.e., an int) and returns how many dates in the list are in the given month. *)
fun number_in_month(dl : (int * int * int) list, month : int) =
    if null dl then
	0
    else if (#2 (hd dl)) = month then
	1 + number_in_month((tl dl), month)
    else
	number_in_month((tl dl), month)

(* 3. Write a function number_in_months that takes a list of dates and a list
      of months (i.e., an int list) and returns the number of dates in the list
      of dates that are in any of the months in the list of months. Assume the list
      of months has no number repeated. Hint: Use your answer to the previous problem. *)
fun number_in_months(dl : (int * int * int) list, ml : int list) =
    if null ml then
	0
    else
	number_in_month(dl, (hd ml)) + number_in_months(dl, (tl ml))

(* 4. Write a function dates_in_month that takes a list of dates and a month
      (i.e., an int) and returns a list holding the dates from the argument list of
      dates that are in the month. The returned list should contain dates in the order
      they were originally given. *)
fun dates_in_month(dl : (int * int * int) list, month : int) =
    if null dl then
	[]
    else if (#2 (hd dl)) = month then
	(hd dl) :: dates_in_month((tl dl), month)
    else
	dates_in_month((tl dl), month)

(* 5. Write a function dates_in_months that takes a list of dates and a list of
      months (i.e., an int list) and returns a list holding the dates from the argument
      list of dates that are in any of the months in the list of months. Assume the
      list of months has no number repeated. Hint: Use your answer to the previous
      problem and SML’s list-append operator (@). *)
fun dates_in_months(dl : (int * int * int) list, ml : int list) =
    if null ml then
	[]
    else
	dates_in_month(dl, (hd ml)) @ dates_in_months(dl, (tl ml))

(* 6. Write a function get_nth that takes a list of strings and an int n and returns
      the nth element of the list where the head of the list is 1st. Do not worry
      about the case where the list has too few elements: your function may apply
      hd or tl to the empty list in this case, which is okay. *)
fun get_nth(sl : string list, n : int) =
    if n = 1 then
	hd sl
    else
	get_nth((tl sl), n - 1)

(* 7. Write a function date_to_string that takes a date and returns a string of
      the form January 20, 2013 (for example). Use the operator ^ for concatenating
      strings and the library function Int.toString for converting an int to a string.
      For producing the month part, do not use a bunch of conditionals. Instead, use a
      list holding 12 strings and your answer to the previous problem. For consistency,
      put a comma following the day and use capitalized English month names: January,
      February, March, April, May, June, July, August, September, October, November,
      December *)
fun date_to_string(date : int * int * int) =
    let val month_list = ["January", "February", "March", "April", "May", "June",
			  "July", "August", "September", "October", "November", "December"]
    in
	get_nth(month_list, (#2 date)) ^ " " ^
	Int.toString((#3 date)) ^ ", " ^ 
	Int.toString((#1 date))
    end

(* 8. Write a function number_before_reaching_sum that takes an int called sum,
      which you can assume is positive, and an int list, which you can assume contains
      all positive numbers, and returns an int. You should return an int n such that
      the first n elements of the list add to less than sum, but the first n + 1 elements
      of the list add to sum or more. Assume the entire list sums to more than the passed
      in value; it is okay for an exception to occur if this is not the case. *)
fun number_before_reaching_sum(sum : int, int_list : int list) =
    if null int_list orelse sum <= (hd int_list) then
	0
    else
	1 + number_before_reaching_sum(sum - (hd int_list), (tl int_list))

(* 9. Write a function what_month that takes a day of year (i.e., an int between 1 and 365)
      and returns what month that day is in (1 for January, 2 for February, etc.). Use a
      list holding 12 integers and your answer to the previous problem. *)
fun what_month(day : int) =
    let val days_list = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    in 
	1 + number_before_reaching_sum(day, days_list)
    end

(* 10. Write a function month_range that takes two days of the year day1 and day2 and returns
       an int list [m1,m2,...,mn] where m1 is the month of day1, m2 is the month of day1+1,
       ..., and mn is the month of day day2. Note the result will have length day2 - day1 + 1
       or length 0 if day1>day2. *)
fun month_range(from : int, to : int) =
    if from > to then
	[]
    else
	what_month(from) :: month_range(from + 1, to)

(* 11. Write a function oldest that takes a list of dates and evaluates to an (int*int*int)
       option. It evaluates to NONE if the list has no dates and SOME d if the date d is
       the oldest date in the list. *)
fun oldest(date_list : (int * int * int) list) =
    if null date_list then
	NONE
    else
	let val t_oldest = oldest((tl date_list))
	in
	    if isSome t_oldest andalso is_older(valOf t_oldest, hd date_list) then
		t_oldest
	    else
		SOME (hd date_list)
	end

(* 12. Challenge Problem: Write functions number_in_months_challenge and 
       dates_in_months_challenge that are like your solutions to problems 3 and 5 except
       having a month in the second argument multiple times has no more effect than having
       it once. (Hint: Remove duplicates, then use previous work.) *)
fun number_in_months_challenge(date_list : (int * int * int) list, month_list : int list) =
    let fun number_in_months(date : int * int * int, month_list : int list) =
	    if null month_list then
		0
	    else if (#2 date) = (hd month_list) then
		1
	    else
		number_in_months(date, tl month_list)
    in
	if null date_list then
	    0
	else
	    number_in_months(hd date_list, month_list) +
	    number_in_months_challenge(tl date_list, month_list)
    end

fun dates_in_months_challenge(date_list : (int * int * int) list, month_list : int list) =
    let fun is_in_month(date : int * int * int, month_list : int list) =
	    if null month_list then
		false
	    else
		#2 date = hd month_list orelse is_in_month(date, tl month_list)
    in
	if null date_list then
	    []
	else if is_in_month(hd date_list, month_list) then
	    (hd date_list) :: dates_in_months_challenge(tl date_list, month_list)
	else
	    dates_in_months_challenge(tl date_list, month_list)
    end

(* 13. Challenge Problem: Write a function reasonable_date that takes a date and determines
       if it describes a real date in the common era. A “real date” has a positive year
       (year 0 did not exist), a month between 1 and 12, and a day appropriate for the month.
       Solutions should properly handle leap years. Leap years are years that are either
       divisible by 400 or divisible by 4 but not divisible by 100. (Do not worry about days
       possibly lost in the conversion to the Gregorian calendar in the Late 1500s.) *)
fun reasonable_date(date : int * int * int) =
    let val days_list = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
	val days_leap_list = [31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
	fun is_leap_year(year : int) =
	    year mod 400 = 0 orelse (year mod 4 = 0 andalso year mod 100 <> 0)
	fun get_nth(int_list : int list, nth : int) =
	    if nth = 1 then
		hd int_list
	    else
		get_nth(tl int_list, nth - 1)
	val y = #1 date
	val m = #2 date
	val d = #3 date
    in
	y > 0 andalso
	(m > 0 andalso m < 13) andalso
	d > 0 andalso
	((is_leap_year(y) andalso 
	  d <= get_nth(days_leap_list, m)) orelse d <= get_nth(days_list, m))
    end
