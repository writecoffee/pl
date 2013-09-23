#lang pyret/whalesong

C = cs173.calculate-locals
parse = cs173.calculate-locals.parse

pids = set([])

fun parse-and-calculate-locals(prog :: String) -> Set<String>:
  calculate-locals(parse(read-sexpr(prog)))
end

fun calculate-locals(expr :: C.Expr) -> Set<String>:
  interpret-locals(expr, pids)
where:
  parse-and-calculate-locals('((fun (x) (@)) 4)') is set(["x"])
end

fun interp-params(params :: List<String>, possible-ids :: Set<String>) -> Set<String>:
  cases (List<String>) params:
    | empty =>
      possible-ids
    | link(ae, a-nxt) =>
      interp-params(a-nxt, possible-ids.add(ae))
  end
end

fun interpret-locals(expr :: C.Expr, possible-ids :: Set<String>) -> Set<String>:
  cases (C.Expr) expr:
    | hole =>
      possible-ids
    | num(n) =>
      possible-ids
    | str(s) =>
      possible-ids
    | id(s) =>
      possible-ids.add(s)
    | app(f, al) =>
      interpret-locals(f.body, interp-params(f.params, possible-ids))
  end
end
