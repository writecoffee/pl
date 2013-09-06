#lang pyret/whalesong

# 2 -- Function
fun add1(x :: Number):
    doc: "this function adds 1 to its argument"
    x + 1
end

print(add1)

# 3 -- Testing
fun exp(x :: Number, y :: Number):
    doc: "exp raises x to the yth power; y must be positive"
    if y == 0:
        1
    else:
        # warning: on y < 0, this will infinite loop!
        x * exp(x, y - 1)
    end
where:
    exp(1, 0) is 1
    exp(10, 0) is 1
    exp(10, 1) is 10
    exp(10, 2) is 100
end

# 4 -- Values, Data-types and Operators
data MyList:
    | my-empty
    | my-link(first, rest :: MyList)
where:
    my-link(1, my-link(2, my-empty))
    my-link(1, my-link(true, my-link(nothing, my-empty)))
    my-empty
end

fun length(l :: List) -> Number:
    cases(List) l:
        | empty => 0
        | link(f, r) => 1 + length(r)
    end
where:
    length(empty) is 0
    length(link(1, empty)) is 1
    length(link(1, link(2, empty))) is 2
end

check:
    empty is []
    link(1, empty) is [1]
    link(1, link(2, link(3, empty))) is [1, 2, 3]
end

# You saw the binary + operator above. This is defined for numbers,
# strings, and lists. We have other common math operators defined on numbers,
# and boolean and, or, and not defined on boolean values. '==' works on all values,
# as does <> (a <> b is the same as negating (a == b)).
fun complicated(a :: Number) -> Number:
    (10 - (a * 2)) / 2
where:
    complicated(10) is -5
    complicated(3) is 2
    complicated(4) is 1
end

# There is an important rule at play above:
# no binary operators may be mixed without parentheses used.
# There is no defined precidence, and it is an error to write mixed binary expressions.
print((1 + 2) - 3)

# 5 -- For
check:
    doubled-numbers = for map(elt from[1, 2, 3]):
        elt * 2
    end

    doubled-numbers is [2,4,6]

    small-numbers = for filter(number from [1,2,3,4,5,6,7,8,9,10]):
        number < 6
    end

    small-numbers is [1, 2, 3, 4, 5]

    sum-of-numbers = for fold(sum from 0, elt from [1, 2, 3]):
        sum + elt
    end

    sum-of-numbers is 6
end
