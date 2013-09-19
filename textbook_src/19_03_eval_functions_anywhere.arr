#lang pyret/whalesong


############################################################################
# So, functions are a distinct kind of value than a nubmer. But we can allow
# function values to appear in the function position of an application.

data Binding:
  | bind (name :: String, value :: Number)
end
 
mt-env = []
xtnd-env = link


data Value:
  | numV (n :: Number)
  | closV (f :: Expr, e :: List<Binding>) # ExprC must be an fdC
end

data ExprC:
  | numC (n :: Number)
  | plusC (l :: ExprC, r :: ExprC)
  | multC (l :: ExprC, r :: ExprC)
  | idC (s :: String)
  | fdC (arg :: String, body :: ExprC)
  | appC (f :: ExprC, a :: ExprC)
end

##########################################################################
#
# Hey! A function value needs to remember the substitutions that have already
# been applied to it. Because we're representing substitutions using an
# environment, a function value therefore needs to be bundled with an
# environment. 
#
# fun interp(e :: ExprC, nv :: List<Binding>):
#   cases (ExprC) e:
#     | numC(n) => numV(n)
#     | plusC(l, r) => plus-v(interp(l, nv), interp(r, nv))
#     | multC(l, r) => mult-v(interp(l, nv), interp(r, nv))
#     | idC(s) => lookup(s, nv)
#     | fdC(_, _) => e
#     | appC(f, a) =>
#       fd = interp(f, nv)
#       arg-val = interp(a, nv)
#       interp(fd.body, xtnd-env(bind(fd.arg, arg-val), mt-env))
#   end
# end
#
# And here comes the resulting data structure -- closure.
#
# Now our interpreter returns either number or closures, see (1) and (2)
#

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


fun plus-v(v1, v2): numV(v1.n + v2.n) end
fun mult-v(v1, v2): numV(v1.n * v2.n) end

fun interp(e :: ExprC, nv :: List<Binding>) -> Value:
  cases (ExprC) e:
    | numC(n) => numV(n)        # (1)
    | plusC(l, r) => plus-v(interp(l, nv), interp(r, nv))
    | multC(l, r) => mult-v(interp(l, nv), interp(r, nv))
    | idC(s) => lookup(s, nv)
    | fdC(_, _) => closV(e, nv) # (2)
    | appC(f, a) =>
        clos = interp(f, nv)
        arg-val = interp(a, nv)
        interp(clos.f.body, xtnd-env(bind(clos.f.arg, arg-val), clos.e))
  end
end

check:
  dbl = fdC("x", plusC(idC("x"), idC("x")))
  quad = fdC("x", appC(dbl, appC(dbl, idC("x"))))
  c5 = fdC("_", numC(5))
  fun i(e): interp(e, mt-env) end
  i(plusC(numC(5), appC(quad, numC(3)))) is 17
  i(multC(appC(c5, numC(3)), numC(4))) is 20
  i(plusC(numC(10), appC(c5, numC(10)))) is 15
  i(plusC(numC(10), appC(dbl, plusC(numC(1), numC(2)))))
    is 16
  i(plusC(numC(10), appC(quad, plusC(numC(1), numC(2)))))
    is 22
end
