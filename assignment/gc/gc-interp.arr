#lang pyret

provide *

import "gc-data.arr" as gc
import "gc-collector.arr" as GC

parse = gc.parse

numE = gc.numE
idE = gc.idE
cifE = gc.cifE
letE = gc.letE
lamE = gc.lamE
appE = gc.appE
plusE = gc.plusE
pairE = gc.pairE
leftE = gc.leftE
rightE = gc.rightE
setLeftE = gc.setLeftE
setRightE = gc.setRightE
gcE = gc.gcE
Expr = gc.Expr

Env = gc.Env
env = gc.env

Loc = gc.Loc
Result = gc.Result
result = gc.result

Bind = gc.Bind
bind = gc.bind

Box = gc.Box
box = gc.box

Runtime = gc.Runtime
make-runtime = gc.make-runtime

garbage-collect = GC.collect-garbage
alloc-num = GC.alloc-num
alloc-pair = GC.alloc-pair
alloc-closure = GC.alloc-closure

fun interp(runtime :: Runtime, init-prog :: String) -> Loc:

  fun add-temp(loc :: Box<Loc>, stack :: List<Env>) -> List<Env>:
    new-env = cases(Env) stack.first:
      | env(bindings, temps) => env(bindings, link(loc, temps))
    end
    link(new-env, stack.rest)
  end

  fun add-binding(name :: String, loc :: Box<Loc>, stack :: List<Env>)
    -> List<Env>:
    new-env = cases(Env) stack.first:
      | env(bindings, temps) =>
        env(link(bind(name, loc), bindings), temps)
    end
    link(new-env, stack.rest)
  end

  fun add-env(the-env :: Env, stack :: List<Env>) -> List<Env>:
    link(the-env, stack)
  end

  fun check-cell(loc :: Loc, expected :: String):
    cell = runtime.memory.get(loc)
    when cell <> expected:
      raise("interp: expected " + expected
            + ", but found " + torepr(cell)
            + " at " + torepr(loc))
    end
  end

  fun get-num(loc :: Loc) -> Number:
    check-cell(loc, "num")
    runtime.memory.get(loc + 1)
  end

  fun get-lam(loc :: Loc) -> Expr:
    check-cell(loc, "clos")
    runtime.memory.get(loc + 1)
  end

  fun get-left(loc :: Loc) -> Loc:
    check-cell(loc, "pair")
    runtime.memory.get(loc + 1)
  end

  fun get-right(loc :: Loc) -> Loc:
    check-cell(loc, "pair")
    runtime.memory.get(loc + 2)
  end

  fun set-left(pair-loc :: Loc, val-loc :: Loc) -> Loc:
    check-cell(pair-loc, "pair")
    runtime.memory.set(pair-loc + 1, val-loc)
    val-loc
  end

  fun set-right(pair-loc :: Loc, val-loc :: Loc) -> Loc:
    check-cell(pair-loc, "pair")
    runtime.memory.set(pair-loc + 2, val-loc)
    val-loc
  end

  fun lookup-id(id :: String, stack :: List<Env>) -> Loc:
    the-env = stack.first
    maybebind = the-env.bindings.find(fun(b): b.name == id;)
    cases(Option<Bind>) maybebind:
      | some(b) => b.loc!v
      | none => raise("Unbound identifier: " + torepr(id))
    end
  end

  fun cells-to-env(loc :: Loc) -> Env:
    env-size = runtime.memory.get(loc)
    env-base = loc + 1
    env-bindings = for fold(bindings from [], i from range(0, env-size)):
      id = runtime.memory.get(env-base + (2 * i))
      val = runtime.memory.get(env-base + (2 * i) + 1)
      link(bind(id, box(val)), bindings)
    end
    env(env-bindings, [])
  end

  fun interp-full(stack :: List<Env>, prog :: Expr) -> Loc:
    cases(Expr) prog:
      | numE(n) =>
          alloc-num(runtime, stack, n)
      | lamE(name, body) =>
          alloc-closure(runtime, stack, prog, stack.first)
      | appE(lam, arg) =>
          lam-loc = box(interp-full(stack, lam))
          arg-loc = box(interp-full(add-temp(lam-loc, stack), arg))
          the-fun = get-lam(lam-loc!v)
          the-env = cells-to-env(lam-loc!v + 2)
          stack2 = add-binding(the-fun.param, arg-loc, add-env(the-env, stack))
          interp-full(stack2, the-fun.body)
      | plusE(left, right) =>
          n1 = get-num(interp-full(stack, left))
          n2 = get-num(interp-full(stack, right))
          alloc-num(runtime, stack, n1 + n2)
      | idE(id) => lookup-id(id, stack)
      | letE(name, expr, body) =>
          loc = box(interp-full(stack, expr))
          interp-full(add-binding(name, loc, stack), body)
      | cifE(cond, consq, altern) =>
          cond-loc = interp-full(stack, cond)
          if get-num(cond-loc) <> 0:
            interp-full(stack, consq)
          else:
            interp-full(stack, altern)
          end
      | pairE(left, right) =>
          left-loc = box(interp-full(stack, left))
          left-stack = add-temp(left-loc, stack)
          right-loc = box(interp-full(left-stack, right))
          right-stack = add-temp(right-loc, left-stack)
          alloc-pair(runtime, right-stack, left-loc!v, right-loc!v)
      | doE(stmts) =>
          for fold(init from nothing, stmt from stmts):
            interp-full(stack, stmt)
          end
      | leftE(pair) =>
          pair-loc = interp-full(stack, pair)
          get-left(pair-loc)
      | rightE(pair) =>
          pair-loc = interp-full(stack, pair)
          get-right(pair-loc)
      | setLeftE(pair, new-val) =>
          pair-loc = box(interp-full(stack, pair))
          pair-stack = add-temp(pair-loc, stack)
          val-loc = interp-full(pair-stack, new-val)
          set-left(pair-loc!v, val-loc)
      | setRightE(pair, new-val) =>
          pair-loc = box(interp-full(stack, pair))
          pair-stack = add-temp(pair-loc, stack)
          val-loc = interp-full(pair-stack, new-val)
          set-right(pair-loc!v, val-loc)
      | gcE(expr) =>
          garbage-collect(stack, runtime)
          interp-full(stack, expr)
    end
  end

  interp-full([env([], [])], parse(read-sexpr(init-prog)))
end

fun eval(prog :: String, size :: Number) -> Result:
  rt = make-runtime(size)
  result(interp(rt, prog), rt)
end
