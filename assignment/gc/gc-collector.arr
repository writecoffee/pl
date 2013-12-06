#lang pyret

provide {collect-garbage: collect-garbage,
         alloc-num: alloc-num,
         alloc-pair: alloc-pair,
         alloc-closure: alloc-closure} end

import "gc-data.arr" as gcd

DEBUG = false
CLEAR-HALF = false

print-heap = gcd.print-heap
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
Bind = gcd.Bind

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

fun alloc-closure(
      rt :: Runtime,
      stack :: List<Env>,
      lam :: Expr,
      lam-env :: Env) -> Loc:

  id-vals = for fold(result from [], binding from lam-env.bindings):
    result.append([binding.name, binding.loc!v])
  end
  alloc(rt, stack, ["clos", lam, lam-env.bindings.length()]  + id-vals)
end

fun print-stack(stack :: List<Env>):
  when DEBUG:
    stack.each(
      fun (env-elem :: Env):
        var pstr :: String = ""
        env-elem.bindings.each(
          fun (bind-elem :: Bind):
            pstr := pstr + "{"
                         + bind-elem.name
                         + ": "
                         + "LOC(" + torepr(bind-elem.loc!v) + ")"
                         + "}; "
          end
        )
        print(pstr)
      end
    )
  end
end

fun move(dtype :: String, read-loc :: Loc, write-loc :: Loc, mem :: Array, rt :: Runtime):
  if dtype == "fwd":
    {
      new-loc : mem.get(read-loc + 1),
      new-off : 0
    }
  else if dtype == "num":
    nval = mem.get(read-loc + 1)
    dry-write(rt, write-loc, ["num", nval])
    dry-write(rt, read-loc, ["fwd", write-loc])
    {
      new-loc : write-loc,
      new-off : 2
    }
  else if dtype == "pair":
    lloc = mem.get(read-loc + 1)
    rloc = mem.get(read-loc + 2)
    ltype = mem.get(lloc)
    rtype = mem.get(rloc)
    dry-write(rt, write-loc, ["pair"])
    dry-write(rt, read-loc, ["fwd", write-loc])

    lret = move(ltype, lloc, write-loc + 3, mem, rt)
    new-lloc = lret.new-loc
    new-loff = lret.new-off
    rret = move(rtype, rloc, write-loc + 3 + new-loff, mem, rt)
    new-rloc = rret.new-loc
    new-roff = rret.new-off

    dry-write(rt, write-loc + 1, [new-lloc, new-rloc])
    {
      new-loc : write-loc,
      new-off : 3 + new-loff + new-roff
    }
  else if dtype == "clos":
    clo-expr = mem.get(read-loc + 1)
    clo-size = mem.get(read-loc + 2)
    dry-write(rt, write-loc, ["clos", clo-expr, clo-size])
    dry-write(rt, read-loc, ["fwd", write-loc])

    var new-boff = 0
    wbeg = write-loc + 3
    next-free = wbeg + (clo-size * 2)
    rbeg = read-loc + 3
    for each(i from range(0, clo-size)):
      clo-bname = mem.get(rbeg + (i * 2))
      clo-bloc = mem.get(rbeg + (i * 2) + 1)
      clo-btype = mem.get(clo-bloc)
      bret = move(clo-btype, clo-bloc, next-free + new-boff, mem, rt)
      new-clo-bloc = bret.new-loc
      new-clo-boff = bret.new-off
      dry-write(rt, wbeg + (i * 2), [clo-bname, new-clo-bloc])
      new-boff := new-boff + new-clo-boff
    end
    {
      new-loc : write-loc,
      new-off : 3 + (clo-size * 2) + new-boff
    }
  else:
    data-loc = mem.get(read-loc + 1)
    data-type = mem.get(data-loc)
    move(data-type, data-loc, write-loc, mem, rt)
  end
end

fun check-offset(rt :: Runtime, cell-size :: Number):
  if rt!front-half:
    when (rt!offset + cell-size) > (rt.memory.length() / 2):
      raise("out-of-memory")
    end
  else:
    when (rt!offset + cell-size) > rt.memory.length():
      raise("out-of-memory")
    end
  end
end

fun alloc(rt :: Runtime, stack :: List<Env>, cells :: List) -> Loc:
  size = cells.length()
  mem = rt.memory
  if has-enough-space(rt, size):
    write(rt, rt!offset, cells)
  else:
    when DEBUG:
      print("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$")
      print("Begin half-space swap for adding: " + torepr(cells))
      print("____________________________ STACK ______________________________")
      print-stack(stack)
      print("____________________________ HEAP  ______________________________")
      print(rt.memory)
    end
    # update offset to another hemisphere
    if rt!front-half:
      rt!{offset: (mem.length() / 2)}
      rt!{front-half: false}
    else:
      rt!{offset: 0}
      rt!{front-half: true}
    end
    # copy the stack
    stack.each(
      fun (env-elem :: Env):
        env-elem.bindings.each(
          fun (bind-elem :: Bind):
            loc = bind-elem.loc!v
            dtype = mem.get(loc)
            ret = move(dtype, loc, rt!offset, mem, rt)
            new-loc = ret.new-loc
            new-off = ret.new-off
            rt!{offset: (rt!offset + new-off)}
            bind-elem.loc!{v: new-loc}
          end
        )
        env-elem.temporaries.each(
          fun (temp-elem :: Box<Loc>):
            loc = temp-elem!v
            dtype = mem.get(loc)
            ret = move(dtype, loc, rt!offset, mem, rt)
            new-loc = ret.new-loc
            new-off = ret.new-off
            rt!{offset: (rt!offset + new-off)}
            temp-elem!{v: new-loc}
          end
        )
      end
    )
    # clear half of the memory for debug issue
    when CLEAR-HALF:
      if rt!front-half:
        for each(i from range(mem.length() / 2, mem.length())):
          mem.set(i, 0)
        end
      else:
        for each(i from range(0, mem.length() / 2)):
          mem.set(i, 0)
        end
      end
    end
    check-offset(rt, cells.length())
    # the pair element got moved
    var target-cells = cells
    when (cells.get(0) == "pair") and (mem.get(cells.get(1)) == "fwd"):
      new-lloc = mem.get(cells.get(1) + 1)
      new-rloc = mem.get(cells.get(2) + 1)
      target-cells := ["pair", new-lloc, new-rloc]
    end
    # the closure bindings got moved
    when (cells.get(0) == "clos") and (cells.get(2) > 0) and (mem.get(cells.get(4)) == "fwd"):
      binds = for fold(idi from [], i from range(0, cells.get(2))):
        idi.append([cells.get(3 + (i * 2)), mem.get(cells.get(3 + (i * 2) + 1) + 1)])
      end
      target-cells := ["clos", cells.get(1), cells.get(2)] + binds
    end
    tmp-ret = write(rt, rt!offset, target-cells)
    when DEBUG:
      print("_________________________________________________________________")
      print("Done with half-space swap and mem allocation")
      print("________________________NEW HEAP ________________________________")
      print(rt.memory)
      print("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$")
    end
    tmp-ret
  end
end

fun dry-write(rt :: Runtime, offset :: Number, cells :: List) -> Number:
  for each(i from range(0, cells.length())):
    rt.memory.set(offset + i, cells.get(i))
  end
  offset + cells.length()
end

fun write(rt :: Runtime, loc :: Loc, cells :: List) -> Loc:
  for each(cell from cells):
    rt.memory.set(rt!offset, cell)
    rt!{offset: rt!offset + 1}
  end
  loc
end
