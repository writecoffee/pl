#lang pyret

import "gc-interp.arr" as gc
import "gc-data.arr" as gcd

eval = gc.eval
runtime = gcd.runtime
Result = gcd.Result
result = gcd.result
Loc = Number
print-heap = gcd.print-heap

IS_DEBUG = true

### Helper functions for writing tests ###

fun mk-result(loc, mem): result(loc, runtime(mem, 0, false));

fun heap-error(loc, mem, expected):
  raise("Expected " + expected + " at location " + loc.tostring() + " but found " + mem.get(loc)._torepr() + " instead")
end

hany = fun(locmem): true end

fun hpair(pred1, pred2):
  fun(locmem):
    cases(Result) locmem:
      | result(loc, rt) =>
        mem = rt.memory
        when not (mem.get(loc) == "pair"): heap-error(loc, mem, "pair tag");
        pred1(result(mem.get(loc + 1), rt))
        pred2(result(mem.get(loc + 2), rt))
        true
    end
  end
end

fun hnum(n :: Number):
  fun(locmem):
    cases(Result) locmem:
      | result(loc, rt) =>
        mem = rt.memory
        when not (mem.get(loc) == "num"): heap-error(loc, mem, "number tag");
        when not (mem.get(loc + 1) == n): heap-error(loc + 1, mem, n.tostring());
        true
    end
  end
end

data Pair<a, b>:
  | pair(left :: a, right :: b)
end

fun hclos(bind-preds :: List<Pair<String, (Result -> Boolean)>>):
  fun(locmem):
    cases(Result) locmem:
      | result(loc, rt) =>
        mem = rt.memory
        when not (mem.get(loc) == "clos"): heap-error(loc, mem, "clos tag");
        for list.all(bind-pred from bind-preds):
          env-size = mem.get(loc + 2)
          maybe-bind = for find(i from range(loc + 3, loc + 3 + (env-size * 2))):
            (mem.get(i) == bind-pred.left) and bind-pred.right(result(mem.get(i + 1), rt))
          end
          when is-none(maybe-bind): raise("No binding found in closure at " + loc.tostring() + " for identifier " + bind-pred.left._torepr());
          true
        end
    end
  end
end



### Your Tests ###

fun pheap(rt): print(print-heap(rt.runtime));

check:
  fun test-and-print(code, size, pred, isDebug :: Bool):
    fun eval-and-print():
      rt = eval(code, size)
      print("=====================  Heap after =====================")
      print(code)
      print("^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^")
      pheap(rt)
      rt
    end
    fun eval-no-print():
      rt = eval(code, size)
      print("=====================  Test Case ======================")
      print(code)
      rt
    end
    if isDebug:
      eval-and-print() satisfies pred
    else:
      eval-no-print() satisfies pred
    end
  end
  fun TEST-BASIC-OPERATION(isDebug :: Bool):
    test-and-print('
      (+ 1 2)
    ', 14, hnum(3), isDebug)
    test-and-print('
      (pair 3 4)
    ', 14, hpair(hnum(3), hnum(4)), isDebug)
    test-and-print('
      (fun (my-param) my-param)
    ', 24, hclos([]), isDebug)
    test-and-print('
      ((fun (my-param) my-param) 9)
    ', 24, hnum(9), isDebug)
    test-and-print('
      (let (x 9)
           x)
    ', 8, hnum(9), isDebug)
    test-and-print('
      (let (x 9)
           (let (y 10)
                x))
    ', 8, hnum(9), isDebug)
    test-and-print('
      (let (x 9)
           (let (my-fun (fun (y) x))
                x))
    ', 80, hnum(9), isDebug)
    test-and-print('
      (let (x 9)
           (let (my-fun (fun (y) x))
                (my-fun 777)))
    ', 80, hnum(9), isDebug)
    test-and-print('
      (if 1 1 0)
    ', 10, hnum(1), isDebug)
    test-and-print('
      (if 0 1 0)
    ', 10, hnum(0), isDebug)
    test-and-print('
      (let (x 9)
           (let (my-fun (fun (y) y))
                (do (my-fun 777)
                    (my-fun 666)
                    (my-fun 555))))
    ', 80, hnum(555), isDebug)
    test-and-print('
      (let (x 9)
           (let (my-fun (fun (y) (pair x y)))
                (left (my-fun 777))))
    ', 80, hnum(9), isDebug)
    test-and-print('
      (let (x 9)
           (let (my-fun (fun (y) (pair x y)))
                (right (my-fun 777))))
    ', 80, hnum(777), isDebug)
    test-and-print('
      (let (x 9)
           (let (my-fun (fun (y) (pair x y)))
                (set-left (my-fun 777) 999)))
    ', 80, hnum(999), isDebug)
    test-and-print('
      (let (x 9)
           (let (my-fun (fun (y) (pair x y)))
                (set-right (my-fun 777) 888)))
    ', 80, hnum(888), isDebug)
  end
  TEST-BASIC-OPERATION(IS_DEBUG)

end
