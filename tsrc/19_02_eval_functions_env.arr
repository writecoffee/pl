#lang pyret/whalesong

data FunDefC:
  | fdC (name :: String, arg :: String, body :: ExprC)
end

data ExprC:
  | numC (n :: Number)
  | plusC (l :: ExprC, r :: ExprC)
  | multC (l :: ExprC, r :: ExprC)
  | idC (s :: String)
  | appC (f :: String, a :: ExprC)
end

###################################################################################
# There’s difficulty with using substitution, which is the number of times we
# traverse the source program. It would be nice to have to traverse only those
# parts of the program that are actually evaluated, and then, only when necessary.
# But substitution traverses everything—unvisited branches of conditionals,
# for instance—and forces the program to be traversed once for substitution
# and once again for interpretation. So here comes the environment.
#
# The environment should map names to answers.
#

data Binding:
  | bind (name :: String, value :: Number)
end
 
mt-env = []
xtnd-env = link

###################################################################################


fun interp(e :: ExprC, nv :: List<Binding>, fds :: List<FunDefC>) -> Number:
  cases (ExprC) e:
    | numC(n) => n
    | plusC(l, r) => interp(l, nv, fds) + interp(r, nv, fds)
    | multC(l, r) => interp(l, nv, fds) * interp(r, nv, fds)
    | idC(s) => lookup(s, nv)
    | appC(f, a) =>
      fd = get-fundef(f, fds)
      arg-val = interp(a, nv, fds)
      interp(fd.body, xtnd-env(bind(fd.arg, arg-val), mt-env), fds)
  end
end

fun lookup(s :: String, nv :: List<Binding>) -> Number:
  cases (List<Binding>) nv:
    | empty => raise("unbound identifier: " + s)
    | link(f, r) =>
      if s == f.name:
        f.value
      else:
        lookup(s, r)
      end
  end
end


fun get-fundef(name :: String, fds :: List<FunDefC>) -> FunDefC:
  cases (List) fds:
    | empty => raise("couldn't find function")
    | link(f, r) =>
      if f.name == name:
        f
      else:
        get-fundef(name, r)
      end
  end
end

check:
  f1 = fdC("double", "x", plusC(idC("x"), idC("x")))
  f2 = fdC("quadruple", "x", appC("double", appC("double", idC("x"))))
  f3 = fdC("const5", "_", numC(5))
  funs = [f1, f2, f3]
  fun i(e): interp(e, mt-env, funs) end
  i(plusC(numC(5), appC("quadruple", numC(3)))) is 17
  i(multC(appC("const5", numC(3)), numC(4))) is 20
  i(plusC(numC(10), appC("const5", numC(10)))) is (10 + 5)
  i(plusC(numC(10), appC("double", plusC(numC(1), numC(2)))))
    is (10 + 3 + 3)
  i(plusC(numC(10), appC("quadruple", plusC(numC(1), numC(2)))))
    is (10 + 3 + 3 + 3 + 3)
  interp(appC("f1", numC(3)), mt-env,
    [fdC("f1", "x", appC("f2", numC(4))),
     fdC("f2", "y", plusC(idC("x"), idC("y")))])
    raises "unbound identifier: x"
end
