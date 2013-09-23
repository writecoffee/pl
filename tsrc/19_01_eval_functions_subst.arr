#lang pyret/whalesong

# expression

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

fun interp(e :: ExprC, fds :: List<FunDefC>) -> Number:
  cases (ExprC) e:
    | numC(n) => n
    | plusC(l, r) => interp(l, fds) + interp(r, fds)
    | multC(l, r) => interp(l, fds) * interp(r, fds)
    | idC(s) => raise("unbound identifier")
    | appC(f, a) => 
      fd = get-fundef(f, fds)
      interp(subst(a, fd.arg, fd.body), fds)
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

fun subst(with :: ExprC, at :: String, in :: ExprC) -> ExprC:
  cases (ExprC) in:
    | numC(n) => in
    | plusC(l, r) => plusC(subst(with, at, l), subst(with, at, r))
    | multC(l, r) => multC(subst(with, at, l), subst(with, at, r))
    | appC(f, a) => appC(f, subst(with, at, a))
    | idC(s) =>
      if s == at:
        with
      else:
        in
      end
  end
end

check:
  l = [
        fdC("double", "x", plusC(idC("x"), idC("x"))),
        fdC("quadruple", "x", appC("double", appC("double", idC("x")))),
        fdC("const5", "_", numC(5)),
        fdC("error", "_", idC("y"))
    ]

  interp(appC("double", numC(0)), l) is 0
  interp(appC("const5", numC(0)), l) is 5
  interp(appC("quadruple", numC(1)), l) is 4
  interp(appC("error", numC(0)), l) raises "unbound identifier"
end
