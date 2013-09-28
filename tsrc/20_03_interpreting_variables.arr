#lang pyret/whalesong

data Value:
  | numV (n :: Number)
  | closV (f :: ExprC, e :: List<Binding>) # ExprC must be an fdC
end

#######################################################################################
# We use 'box' to represent structures. We treat it as a fresh container type.
#
#   --  'box' consumes a value and creates a mutable box containing that value.
#   --  'unbox' consumes a box and returns the value contained in the box.
#   --  'set-box' consumes a box, a new value, and changes the box to contain the value.
#       All subsequent unboxes of that box will now return the new value.
#
#  'box' is the constructor, 'unbox' is the getter, and 'set-box' is the setter.
#
data Box:
  | box (mutable v)
where:
  n1 = box(1)
  n2 = box(2)
  n1!{v : 3}
  n2!{v : 4}
  n1!v is 3
  n2!v is 4
end

#######################################################################################
# Each invocation of mk-counter creates a box only once, which it binds to ctr.
# The closure closes over this one box. All subsequent mutations affect the same box.
#
# Clearly, whatever the environment closes over in the procedure returned by mk-counter 
# must refer to the same box each time. Yet something also needs to make sure that the
# value in that box is different each time! Look at it more carefully:
# it must be lexically the same, but dynamically different. 
#
fun mk-counter():
  ctr = box(0)
  fun():
    ctr!{v : (ctr!v + 1)}
    ctr!v
  end
where:
  l1 = mk-counter()
  l1() is 1
  l1() is 2
end

#######################################################################################
# We need to obtain a fresh value each time, so we need to use a stateful counter.
#
new-loc = mk-counter()

#######################################################################################
# 
data ExprC:
  | numC (n :: Number)
  | plusC (l :: ExprC, r :: ExprC)
  | multC (l :: ExprC, r :: ExprC)
  | varC (s :: String)
  | appC (f :: ExprC, a :: ExprC)
  | fdC (arg :: String, body :: ExprC)
  | setC(v :: String, b :: ExprC)
  | seqC (b1, b2 :: ExprC)
end

#######################################################################################
# Observe that in each of the mutation statements, we are using a complex expression—
# e.g., list.index(l, 0)—rather than a literal or an identifier to obtain the box
# before mutating it (!{v : 1}). 
#
fun make-box-list():
  b0 = box(0)
  b1 = box(1)
  l = [b0, b1]
  list.index(l, 0)!{v : 1}
  list.index(l, 1)!{v : 2}
  l
where:
  l = make-box-list()
  list.index(l, 0)!v is 1
  list.index(l, 1)!v is 2
end


data Binding:
  | bind (name :: String, location :: Number)
end

data Storage:
  | cell (location :: Number, value :: Value)
end

# Env = List<Binding>
mt-env = []
xtnd-env = link

# Sto = List<Storage>
mt-sto = []
xtnd-sto = link

fun plus-v(v1, v2): numV(v1.n + v2.n) end
fun mult-v(v1, v2): numV(v1.n * v2.n) end

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

fun fetch(n :: Number, st :: List<Storage>) -> Value:
  cases (List<Storage>) st:
    | empty => raise("unknown location: " + n)
    | link(f, r) =>
      if n == f.location:
        f.value
      else:
        fetch(n, r)
      end
  end
end

#######################################################################################
# The store is threaded: rather than using the same store in all branches,
# we take the store from one branch and pass it on to the next, and take
# the result and send it back out. This pattern is called store-passing
# style.
#
fun interp(e :: ExprC, nv :: List<Binding>, st :: List<Storage>) -> Value:
  cases (ExprC) e:
    | numC(n) =>
      ret(numV(n), st)
    | plusC(l, r) =>
      lv = interp(l, nv, st)
      rv = interp(r, nv, lv.st)
      ret(plus-v(lv.v, rv.v), rv.st)
    | multC(l, r) =>
      lv = interp(l, nv, st)
      rv = interp(r, nv, lv.st)
      ret(mult-v(lv.v, rv.v), rv.st)
    | idC(s) =>
      ret(fetch(lookup(s, nv), st), st)
    | fdC(_, _) =>
      ret(closV(e, nv), st)
    | setC(v, b) =>
      new-val = interp(b, nv, st)
      var-loc = lookup(v, nv)
      ret(new-val.v, xtnd-sto(cell(var-loc, new-val.v), new-val.st))
    | seqC(b1, b2) =>
      b1-value = interp(b1, nv, st)
      interp(b2, nv, b1-value.st)
    | appC(f, a) =>
      clos = interp(f, nv, st)
      clos-v :: Value = clos.v
      clos-st :: List<Storage> = clos.st
      arg-val = interp(a, nv, clos-st)
      arg-loc = new-loc()
      interp(clos-v.f.body,
        xtnd-env(bind(clos-v.f.arg, arg-loc), clos-v.e),
        xtnd-sto(cell(arg-loc, arg-val.v), arg-val.st))
  end
end

#######################################################################################
# Instead, something else needs to be responsible for maintaining
# the dynamic state of mutated boxes. This latter data structure is called the store.
#
# Like the environment, the store is a partial map. Its domain could be any abstract
# set of names, but it is natural to think of these as numbers, meant to stand for 
# memory locations. This is because the store in the semantics maps directly onto
# (abstracted) physical memory in the machine, which is traditionally addressed by
# numbers. Thus the environment maps names to locations, and the store maps locations 
# to values:

fun ret(v :: Value, st :: List<Storage>): {v : v, st : st};
