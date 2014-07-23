#lang pyret/whalesong

fun append(list1 :: List, list2 :: List) -> List:
  cases(List) list1:
    | empty => (
        if list2 == empty:
          empty
        else:
          append(list2, empty)
        end
      )
    | link(value, nextLink) => (
        if value == empty:
          append(nextLink, list2)
        else:
          link(value, append(nextLink, list2))
        end
      )
  end
where:

  # Here we choose Number as the value type of 'link' in the testing.
  # Because it's wrapped inside link of the List, it should work fine for 
  # any combination/permutation of primitive data (e.g., number, string, boolean)
  # as well as user-defined data types.
  #
  # The argument choices could be boiled down to any pair combination picked from 
  # the set
  #
  # {
  #   empty,
  #   link(value, empty),
  #   link(empty, value),
  #   link(value, List),
  #   link(List, value),
  #   link(List, List)
  # }
  #
  # and theoretically, a list is either empty or a link with an element and another list.
  # It can be generalized to broader and with more "embedded list" use cases once the following 
  # test cases passed.

  append(empty, empty) is []
  
  append(empty, link(1, empty)) is [1]
  append(link(1, empty), empty) is [1]

  append(empty, link(1, link(2, empty))) is [1, 2]
  append(link(1, link(2, empty)), empty) is [1, 2]

  append(link(1, empty), link(2, link(3, empty))) is [1, 2, 3]
  append(link(1, link(2, empty)), link(3, empty)) is [1, 2, 3]

  append(link(1, link(2, empty)), link(3, link(4, empty))) is [1, 2, 3, 4]

  # Also, we should note that the incoming argument with List which contains no element at all
  # (all are 'empty') should be treated as empty. Because the 'list1' and 'list2' are treated
  # seperately and there should be no interleaving between elements stretching across the two 
  # lists, by default we use link and List with value on the left bucket.

  append(link(empty, empty), link(empty, empty)) is []

  append(link(1, empty), link(empty, empty)) is [1]
  append(link(empty, empty), link(1, empty)) is [1]

  append(link(1, link(2, empty)), link(empty, empty)) is [1, 2]
  append(link(empty, empty), link(1, link(2, empty))) is [1, 2]
end

fun quick-sort(l :: List) -> List:
  cases(List) l:
    | empty => empty
    | link(pivot, nextList) =>
        partitioned = partition(fun(elem): elem > pivot end, nextList)
        partitionedSmaller = quick-sort(partitioned.is-false)
        partitionedBigger = quick-sort(partitioned.is-true)
        partitionedSmaller + [pivot] + partitionedBigger
  end
where:
  # empty string
  quick-sort([]) is []
  # 1 element (no parition needed)
  quick-sort([1]) is [1]
  # 2 elements (partition once)
  quick-sort([3,1]) is [1,3]
  # >2 elements (input is in ascending order already)
  quick-sort([1,2,3,4]) is [1,2,3,4]
  # >2 elements (input is in descending order)
  quick-sort([4,3,2,1]) is [1,2,3,4]
  # duplicate elements
  quick-sort([1,1]) is [1,1]
  quick-sort([1,3,1,1,2]) is [1,1,1,2,3]
end
