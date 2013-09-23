#lang pyret/whalesong

C = cs173.calculate-locals
parse = cs173.calculate-locals.parse

fun parse-and-calculate-locals(prog :: String) -> Set<String>:
  calculate-locals(parse(read-sexpr(prog)))
end

fun calculate-locals(expr :: C.Expr) -> Set<String>:
  fun scan-params(params :: List<String>, possible-ids :: Set<String>) -> Set<String>:
    cases (List<String>) params :
      | empty =>
        possible-ids
      | link(ae, a-nxt) =>
        scan-params(a-nxt, possible-ids.add(ae))
    end
  end
  fun scan-expr(se :: C.Expr, possible-ids :: Set<String>) -> Set<String>:
    cases (C.Expr) se :
      | hole =>
        possible-ids
      | num(n) =>
        set([])
      | str(s) =>
        set([])
      | bop(op, l, r) =>
        lr = scan-expr(l, possible-ids)
        rr = scan-expr(r, possible-ids)
        lr.union(rr)
      | cif(c, sq, alt) =>
        cr = scan-expr(c, possible-ids)
        sr = scan-expr(sq, possible-ids)
        ar = scan-expr(alt, possible-ids)
        cr.union(sr).union(ar)
      | id(s) =>
        set([])
      | lam(pl, bd) =>
        scan-expr(bd, scan-params(pl, possible-ids))
      | app(f, al) =>
        scan-expr(f, possible-ids)
      | let(n, e, bd) =>
        new-pid = possible-ids.add(n)
        er = scan-expr(e, possible-ids)
        br = scan-expr(bd, new-pid)
        er.union(br)
    end
  end

  scan-expr(expr, set([]))
where:
  parse-and-calculate-locals('(@)')
    is set([])

  parse-and-calculate-locals('((fun (x) (x)) 4)')
    is set([])

  parse-and-calculate-locals('((fun (x) (@)) 4)')
    is set(["x"])

  parse-and-calculate-locals('
    ((fun (m n)
        (fun (x y z) (@)))
        7 8)
  ') is set(["x", "y", "z", "m", "n"])

  parse-and-calculate-locals('
    ((fun (m n)
        (+ @ m))
        7 8)
  ') is set(["m", "n"])

  parse-and-calculate-locals('
    ((fun (x y z)
        (@))
        m)
  ') is set(["x", "y", "z"])

  parse-and-calculate-locals('
    ((fun (x y)
        (if (== x y) @ 0))
        "hello" "hello")
  ') is set(["x", "y"])

  parse-and-calculate-locals('
    ((fun (x y)
        (if (== x y)
            (fun (m n) (+ m @))
            (fun (o p) (* o p))))
        "hello" "hello")
  ') is set(["x", "y", "m", "n"])

  parse-and-calculate-locals('
    ((fun (x y)
        (let (m (+ x 3)) @)))
  ') is set(["x", "y", "m"])
   
  parse-and-calculate-locals('
    ((fun (x y)
        (let (m (+ @ 3)) (+ x y))))
  ') is set(["x", "y"])

  parse-and-calculate-locals('
    ((fun (x y)
        (let  (temp-var 0) 
              (let (next-var @) "hello-end"))) 9 10)
  ') is set(["x", "y", "temp-var"])
end
