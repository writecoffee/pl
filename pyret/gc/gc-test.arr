#lang pyret

import "gc-interp.arr" as gc
import "gc-data.arr" as gcd

eval = gc.eval
runtime = gcd.runtime
Result = gcd.Result
result = gcd.result
Loc = Number
print-heap = gcd.print-heap

IS_DEBUG = false

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
  fun TEST-FAILED(code, size, error-msg :: String, isDebug :: Bool):
    fun eval-and-print():
      print("===================  (F) Test Case =====================")
      print(code)
      rt = eval(code, size)
      rt
    end
    fun eval-no-print():
      rt = eval(code, size)
      rt
    end
    if isDebug:
      eval-no-print() raises error-msg
    else:
      eval-no-print() raises ""
    end
  end
  fun TEST-PASSED(code, size, pred, isDebug :: Bool):
    fun eval-and-print():
      print("=====================  Test Case ======================")
      print(code)
      rt = eval(code, size)
      print("=====================  Heap after =====================")
      print(code)
      print("^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^")
      pheap(rt)
      rt
    end
    fun eval-no-print():
      rt = eval(code, size)
      rt
    end
    if isDebug:
      eval-and-print() satisfies pred
    else:
      eval-no-print() satisfies pred
    end
  end
  fun test-basic-operation(isDebug :: Bool):
    TEST-PASSED('
      (+ 1 2)
    ', 14, hnum(3), isDebug)
    TEST-PASSED('
      (pair 3 4)
    ', 14, hpair(hnum(3), hnum(4)), isDebug)
    TEST-PASSED('
      (fun (my-param) my-param)
    ', 24, hclos([]), isDebug)
    TEST-PASSED('
      ((fun (my-param) my-param) 9)
    ', 24, hnum(9), isDebug)
    TEST-PASSED('
      (let (x 9)
           x)
    ', 8, hnum(9), isDebug)
    TEST-PASSED('
      (let (x 9)
           (let (y 10)
                x))
    ', 8, hnum(9), isDebug)
    TEST-PASSED('
      (let (x 9)
           (let (my-fun (fun (y) x))
                x))
    ', 80, hnum(9), isDebug)
    TEST-PASSED('
      (let (x 9)
           (let (my-fun (fun (y) x))
                (my-fun 777)))
    ', 80, hnum(9), isDebug)
    TEST-PASSED('
      (if 1 1 0)
    ', 10, hnum(1), isDebug)
    TEST-PASSED('
      (if 0 1 0)
    ', 10, hnum(0), isDebug)
    TEST-PASSED('
      (let (x 9)
           (let (my-fun (fun (y) y))
                (do (my-fun 777)
                    (my-fun 666)
                    (my-fun 555))))
    ', 80, hnum(555), isDebug)
    TEST-PASSED('
      (let (x 9)
           (let (my-fun (fun (y) (pair x y)))
                (left (my-fun 777))))
    ', 80, hnum(9), isDebug)
    TEST-PASSED('
      (let (x 9)
           (let (my-fun (fun (y) (pair x y)))
                (right (my-fun 777))))
    ', 80, hnum(777), isDebug)
    TEST-PASSED('
      (let (x 9)
           (let (my-fun (fun (y) (pair x y)))
                (set-left (my-fun 777) 999)))
    ', 80, hnum(999), isDebug)
    TEST-PASSED('
      (let (x 9)
           (let (my-fun (fun (y) (pair x y)))
                (set-right (my-fun 777) 888)))
    ', 80, hnum(888), isDebug)
  end
  fun test-garbage-collection(isDebug :: Bool):
    TEST-FAILED('
      (let (x 9)
           (let (y 88)
                (do 1 2 3 4 5 6)))
    ', 10, "out-of-memory", isDebug)
    TEST-PASSED('
      (let (x 9)
           (let (my-fun (fun (y) (+ 3 y)))
                (do (my-fun 77))))
    ', 22, hnum(80), isDebug)
    TEST-PASSED('
      (let (x 9)
           (let (my-fun (fun (y) (+ 3 y)))
                (do (my-fun 77)
                    (my-fun 88))))
    ', 22, hnum(91), isDebug)
    TEST-FAILED('
      (let (x 9)
           (let (my-pair (pair 111 222))
                (left my-pair)))
    ', 14, "out-of-memory", isDebug)
    TEST-PASSED('
      (do 999
          888
          (let (my-pair (pair 111 222))
               (left my-pair)))
    ', 20, hnum(111), isDebug)
    TEST-PASSED('
      (do 999
          888
          (let (x 111)
               (let (y 222)
                    (let (my-fun (fun (y) (+ 3 y)))
                         (do (my-fun 77))))))
    ', 30, hnum(80), isDebug)
    TEST-FAILED('
      (do 999
          888
          (let (x 111)
               (let (y 222)
                    (let (my-fun (fun (y) (+ 3 y)))
                         (do (my-fun 77))))))
    ', 28, "out-of-memory", isDebug)
    TEST-PASSED('
      (do 999
          888
          (let (my-pair (pair 111 222))
               (do (set-left my-pair 333)
                   (left my-pair))))
    ', 20, hnum(333), isDebug)
    TEST-PASSED('
      (do 999
          888
          (let (my-pair (pair 111 222))
               (do (set-right my-pair 333)
                   (right my-pair))))
    ', 20, hnum(333), isDebug)
  end
  test-basic-operation(IS_DEBUG)
  test-garbage-collection(IS_DEBUG)

end
