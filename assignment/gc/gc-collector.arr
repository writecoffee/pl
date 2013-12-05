#lang pyret

provide {collect-garbage: collect-garbage,
         alloc-num: alloc-num,
         alloc-pair: alloc-pair,
         alloc-closure: alloc-closure} end

import "gc-data.arr" as gcd

Runtime = gcd.Runtime
runtime = gcd.runtime
Env = gcd.Env
env = gcd.env
lamE = gcd.lamE
numE = gcd.numE
idE = gcd.idE
bind = gcd.bind
Box = gcd.Box
box = gcd.box
Loc = gcd.Loc
Expr = gcd.Expr

fun collect-garbage(program-stack :: List<Env>, rt :: Runtime) -> Nothing:
  nothing
end

fun has-enough-space(rt :: Runtime, size :: Number) -> Boolean:
  max = if rt!front-half: rt.memory.length() / 2
        else: rt.memory.length();
  (rt!offset + size) <= max
end

fun alloc-num(rt :: Runtime, stack :: List<Env>, val :: Number) -> Loc:
  alloc(rt, stack, ["num", val])
end

fun alloc-pair(rt :: Runtime, stack :: List<Env>, left :: Loc, right :: Loc) -> Loc:
  alloc(rt, stack, ["pair", left, right])
end

fun alloc-closure(rt :: Runtime, stack :: List<Env>,
    lam :: Expr, lam-env :: Env) -> Loc:
  id-vals = for fold(result from [], binding from lam-env.bindings):
    result.append([binding.name, binding.loc!v])
  end
  alloc(rt, stack, ["clos", lam, lam-env.bindings.length()]  + id-vals)
end

fun alloc(rt :: Runtime, stack :: List<Env>, cells :: List) -> Loc:
  size = cells.length()
  if has-enough-space(rt, size):
    write(rt, rt!offset, cells)
  else:
    raise("Out of memory!")
  end
end

fun write(rt :: Runtime, loc :: Loc, cells :: List) -> Loc:
  for each(cell from cells):
    rt.memory.set(rt!offset, cell)
    rt!{offset: rt!offset + 1}
  end
  loc
end
