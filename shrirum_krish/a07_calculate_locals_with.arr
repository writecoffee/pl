#lang pyret/whalesong

data Value:
  | numV(value :: Number)
  | strV(value :: String)
  | funV(params :: List<String>, body :: Expr, env :: Env)
  | recV(fields :: List<FieldV>)
end

data FieldV:
  | fieldV(name :: String, value :: Value)
end

data Env:
  | mt-env
  | an-env(name :: String, loc :: String, env :: Env)
end

data Store:
  | mt-store
  | a-store(loc :: String, val :: Value, store :: Store)
end

data Result:
  | result(val :: Value, store :: Store)
end

data Expr:
  | idE(name :: String)
  | numE(value :: Number)
  | strE(value :: String)
  | bopE(op :: Operator, left :: Expr, right :: Expr)
  | cifE(cond :: Expr, consq :: Expr, altern :: Expr)
  | letE(name :: String, expr :: Expr, body :: Expr)
  | lamE(params :: List<String>, body :: Expr)
  | appE(func :: Expr, args :: List<Expr>)
  | assignE(name :: String, expr :: Expr)
  | doE(exprs :: List<Expr>)
  | recordE(fields :: List<Field>)
  | lookupE(rec :: Expr, field-name :: String)
  | extendE(rec :: Expr, field-name :: String, new-value :: Expr)
  | withE(namespace :: Expr, body :: Expr)

  | holeE
end

data Field:
  | fieldE(name :: String, value :: Expr)
end

data Operator:
  | plus
  | minus
  | append
  | str-eq
end


fun parse(prog) -> Expr:
  fun convert-field(sexpr):
    fieldE(sexpr.get(0), convert(sexpr.get(1)))
  end
  fun convert(sexpr):
    if List(sexpr):
      head = sexpr.first
      if head == "string":
        strE(sexpr.get(1))
      else if head == "if":
        cifE(convert(sexpr.get(1)),
                 convert(sexpr.get(2)),
             convert(sexpr.get(3)))
      else if head == "let":
        letE(sexpr.get(1).get(0),
             convert(sexpr.get(1).get(1)),
             convert(sexpr.get(2)))
      else if head == "record":
        recordE(map(convert-field, sexpr.rest))
      else if head == "lookup":
        lookupE(convert(sexpr.get(1)), sexpr.get(2))
      else if head == "extend":
        extendE(convert(sexpr.get(1)),
                sexpr.get(2),
                convert(sexpr.get(3)))
      else if head == "with":
        withE(convert(sexpr.get(1)), convert(sexpr.get(2)))
      else if head == "assign":
        assignE(sexpr.get(1), convert(sexpr.get(2)))
      else if head == "do":
        when is-empty(sexpr.rest):
          raise("Paret: do blocks cannot be empty")
        end
        doE(map(convert, sexpr.rest))
      else if head == "fun":
        lamE(sexpr.get(1), convert(sexpr.get(2)))
      else if head == "+":
        bopE(plus, convert(sexpr.get(1)), convert(sexpr.get(2)))
      else if head == "-":
        bopE(minus, convert(sexpr.get(1)), convert(sexpr.get(2)))
      else if head == "++":
        bopE(append, convert(sexpr.get(1)), convert(sexpr.get(2)))
      else if head == "==":
        bopE(str-eq, convert(sexpr.get(1)), convert(sexpr.get(2)))
      else:
        func = convert(head)
        args = map(convert, sexpr.rest)
        appE(func, args)
      end
    else if Number(sexpr):
      numE(sexpr)
    else if sexpr == "@":
      holeE
    else if String(sexpr):
      idE(sexpr)
    end
  end
  convert(prog)
end

fun parse-and-calculate-locals(prog :: String) -> Set<String>:
  calculate-locals(parse(read-sexpr(prog)))
end

parse-and-calc = parse-and-calculate-locals
fun calculate-locals(expr :: Expr) -> Set<String>:
  data Pid:
    | mt-pid
    | an-pid(name :: String, pid :: Pid)
  end
  fun concat-pid(pid1 :: Pid, pid2 :: Pid) -> Pid:
    cases (Pid) pid1:
      | mt-pid =>
        pid2
      | an-pid(p1-n, p1-ext) =>
        an-pid(p1-n, concat-pid(p1-ext, pid2))
    end
  end
  fun transfer-pid-2-set(t-pid :: Pid):
    cases (Pid) t-pid:
      | mt-pid =>
        set([])
      | an-pid(n, nxt) =>
        set([n]).union(transfer-pid-2-set(nxt))
    end
  end
  fun transfer-param-2-pid(t-params :: List<String>):
    cases (List<String>) t-params:
      | empty =>
        mt-pid
      | link(n, nxt) =>
        an-pid(n, transfer-param-2-pid(nxt))
    end
  end
  fun cal-args-helper(ha-a-l ::  List<Expr>, ha-pid :: Pid, ha-prd :: Pid):
    cases (List<Expr>) ha-a-l:
      | empty =>
        {
          pad : ha-pid,
          pbd : mt-pid
        }
      | link(exp, nxt) =>
        exp-ret = go-cal(exp, ha-pid, ha-prd)
        exp-pad = exp-ret.pad
        if not (exp-pad == mt-pid):
          exp-ret
        else:
          cal-args-helper(nxt, ha-pid, ha-prd)
        end
    end
  end
  fun cal-do-helper(hd-e-l :: List<Expr>, hd-pid :: Pid, hd-prd :: Pid):
    cases (List<Expr>) hd-e-l:
      | empty =>
        {
          pad : hd-pid
        }
      | link(exp, nxt) =>
        exp-ret = go-cal(exp, hd-pid, hd-prd)
        exp-pad = exp-ret.pad
        if not (exp-pad == mt-pid):
          exp-ret
        else:
          cal-args-helper(nxt, hd-pid, hd-prd)
        end
    end
  end
  fun cal-record-helper(hr-f-l :: List<Field>, hr-pid :: Pid, hr-prd :: Pid):
    cases (List<Field>) hr-f-l:
      | empty =>
        {
          pad : mt-pid,
          pbd : mt-pid
        }
      | link(fd, nxt) =>
        fd-ret = go-cal(fd.value, hr-pid, hr-prd)
        fd-pad = fd-ret.pad
        if not (fd-pad == mt-pid):
          {
            pad : fd-pad,
            pbd : mt-pid            # if "@" found as field value,
                                    # discard 'prd' as well as prev accumulated 
          }
        else:
          nxt-ret = cal-record-helper(nxt, hr-pid, hr-prd)
          nxt-pad = nxt-ret.pad
          nxt-pbd = nxt-ret.pbd
          {
            pad : nxt-pad,
            pbd : an-pid(fd.name, nxt-pbd)
          }
        end
    end
  end
  fun go-cal(
      i-prog :: Expr,
      i-pid :: Pid,
      i-prd :: Pid):
    cases (Expr) i-prog:
      | holeE =>
        {
          pad : i-pid,
          pbd : mt-pid
        }
      | numE(n) =>
        {
          pad : mt-pid,
          pbd : mt-pid
        }
      | strE(s) =>
        {
          pad : mt-pid,
          pbd : mt-pid
        }
      | idE(s) =>
        {
          pad : mt-pid,
          pbd : i-prd         # the only case it is needed is 
                              # the id points to a recV
        }
      | letE(id, exp, bd) =>
        exp-ret = go-cal(exp, i-pid, i-prd)
        exp-pad = exp-ret.pad
        exp-pbd = exp-ret.pbd
        if not (exp-pad == mt-pid):
          {
            pad : exp-pad
          }
        else:
          print("letE")
          print(exp-pbd)
          go-cal(bd, an-pid(id, i-pid), concat-pid(exp-pbd, i-prd))
        end
      | bopE(op, l, r) =>
        lv-ret = go-cal(l, i-pid, i-prd)
        lv-pad = lv-ret.pad
        if not (lv-pad == mt-pid):
          lv-ret
        else:
          go-cal(r, i-pid, i-prd)
        end
      | cifE(c, sq, alt) =>
        cond-ret = go-cal(c, i-pid, i-prd)
        cond-pad = cond-ret.pad
        if not (cond-pad == mt-pid):
          cond-ret
        else:
          sq-ret = go-cal(sq, i-pid, i-prd)
          sq-pad = sq-ret.pad
          sq-pbd = sq-ret.pbd
          if not (sq-pad == mt-pid):
            sq-ret
          else:
            alt-ret = go-cal(alt, i-pid, i-prd)
            alt-pad = alt-ret.pad
            alt-pbd = alt-ret.pbd
            {
              pad : alt-pad,
              pbd : concat-pid(sq-pbd, alt-pbd)
            }
          end
        end
      | lamE(p-l, bd) =>
        pl-pad = transfer-param-2-pid(p-l)
        go-cal(bd, concat-pid(pl-pad, i-pid), i-prd)
      | appE(f, a-l) =>
        lam-ret = go-cal(f, i-pid, i-prd)
        lam-pad = lam-ret.pad
        if not (lam-pad == mt-pid):
          lam-ret
        else:
          cal-args-helper(a-l, i-pid, i-prd)
        end
      | assignE(id, exp) =>
        go-cal(exp, i-pid, i-prd)
      | doE(exp-l) =>
        cal-do-helper(exp-l, i-pid, i-prd)
      | recordE(f-l) =>
        cal-record-helper(f-l, i-pid, i-prd)
      | lookupE(r-e, fn) =>
        go-cal(r-e, i-pid, i-prd)
      | extendE(r-e, fn, nv) =>
        rcd-ret = go-cal(r-e, i-pid, i-prd)
        rcd-pad = rcd-ret.pad
        if not (rcd-pad == mt-pid):
          rcd-ret
        else:
          rcd-pbd = rcd-ret.pbd
          {
            pad : i-pid,
            pbd : an-pid(fn, rcd-pbd)
          }
        end
      | withE(ns, bd) =>
        ns-ret = go-cal(ns, i-pid, mt-pid)
        ns-pad = ns-ret.pad
        ns-pbd = ns-ret.pbd
        if not (ns-pad == mt-pid):
          ns-ret
        else:
          go-cal(bd, ns-pbd, i-prd)
        end
    end
  end
  transfer-pid-2-set(go-cal(expr, mt-pid, mt-pid).pad)
where:
#  ##
#  # Test-letE
#  parse-and-calculate-locals('
#    (let (x 1) @)
#  ') is set(["x"])
#  parse-and-calculate-locals('
#    (let (x (+ 1 @)) x)
#  ') is set([])
#  parse-and-calculate-locals('
#    (let (x 3) 
#         (if (== 3 x) @ x))
#  ') is set(["x"])
#  parse-and-calculate-locals('
#    (let (x 3) 
#         (if (== 3 x) 3 @))
#  ') is set(["x"])
#  ##
#  # Test-lamE
#  parse-and-calculate-locals('
#    (fun (x) @)
#  ') is set(["x"])
#  parse-and-calculate-locals('
#    (fun (x y z) @)
#  ') is set(["x", "y", "z"])
#  parse-and-calculate-locals('
#    (fun (x y z)
#         (+ x @))
#  ') is set(["x", "y", "z"])
#  parse-and-calculate-locals('
#    ((fun (x) (@)) 4)
#  ') is set(["x"])
#  parse-and-calculate-locals('
#    ((fun (x y) (+ x y)) 4 @)
#  ') is set([])
#  parse-and-calculate-locals('
#    ((fun (x y) (+ x @)) 4 @)
#  ') is set(["x", "y"])
#  parse-and-calculate-locals('
#    (let (my-id 99)
#         ((fun (x y) (+ x y)) 4 @))
#  ') is set(["my-id"])
#  parse-and-calculate-locals('
#    ((fun (m n)
#          (fun (x y z) (@)))
#        7 8)
#  ') is set(["x", "y", "z", "m", "n"])
#  ##
#  # Test-appE
#  parse-and-calculate-locals('
#    ((fun (m n)
#          (+ @ m))
#          7 8)
#  ') is set(["m", "n"])
#  parse-and-calculate-locals('
#    ((fun (x y z)
#          (@))
#          m)
#  ') is set(["x", "y", "z"])
#  parse-and-calculate-locals('
#    ((fun (x y)
#        (if (== x y) @ 0))
#        "hello" "hello")
#  ') is set(["x", "y"])
#  parse-and-calculate-locals('
#    ((fun (x y)
#        (if (== x y)
#            (fun (m n) (+ m @))
#            (fun (o p) (* o p))))
#        "hello" "hello")
#  ') is set(["x", "y", "m", "n"])
#  parse-and-calculate-locals('
#    ((fun (x y)
#        (let (m (+ x 3)) @)))
#  ') is set(["x", "y", "m"])
#  parse-and-calculate-locals('
#    ((fun (x y)
#        (let (m (+ @ 3)) (+ x y))))
#  ') is set(["x", "y"])
#  parse-and-calculate-locals('
#    ((fun (x y)
#        (let (temp-var 0) 
#             (let (next-var @) "hello-end"))) 9 10)
#  ') is set(["x", "y", "temp-var"])
#  ##
#  # Test-assignE
#  parse-and-calculate-locals('
#    (let (x 1) (assign x @))
#  ') is set(["x"])
#  parse-and-calculate-locals('
#    (let (x 1) (assign x @))
#  ') is set(["x"])
#  parse-and-calculate-locals('
#    (let (myFunc (fun (x) (assign x 1)))
#         (let (y 0) (myFunc @)))
#  ') is set(["myFunc", "y"])
#  ##
#  # Test-doE
#  parse-and-calculate-locals('
#    (do (+ 1 @))
#  ') is set([])
#  parse-and-calculate-locals('
#    (let (x 1)
#         (do (assign x 999)
#             (@)))
#  ') is set(["x"])
#  parse-and-calculate-locals('
#    (let (x 1)
#         (do (assign x @)
#             (+ x 99)))
#  ') is set(["x"])
#  parse-and-calculate-locals('
#    (let (x 1)
#         (do (assign x @)
#             (+ x 99)))
#  ') is set(["x"])
#  ##
#  # Test-recordE/lookupE/extendE
#  parse-and-calculate-locals('
#    (let (my-record (record (x 1)))
#         (lookup @ x))
#  ') is set(["my-record"])
#  parse-and-calculate-locals('
#    (let (my-record (record (x @)))
#         (lookup my-record x))
#  ') is set([])
#  parse-and-calculate-locals('
#    (let (my-first-rcd (record (y "dummy-info-tobe-shadowed")))
#         (let (my-second-rcd (record (x 1) (y 2)))
#              (lookup @ y)))
#  ') is set(["my-first-rcd", "my-second-rcd"])
#  parse-and-calculate-locals('
#    (let (my-first-rcd (record (y "dummy-info-tobe-shadowed")))
#         (let (my-second-rcd (record (x 1) (y @)))
#              (lookup my-first-rcd y)))
#  ') is set(["my-first-rcd"])
#  parse-and-calculate-locals('
#    (let (my-record (record (x 1) (y 3)))
#         (lookup (extend my-record z @) z))
#  ') is set(["my-record"])
#  parse-and-calculate-locals('
#    (let (my-first-rcd (record (y "dummy-info-tobe-shadowed")))
#         (let (my-second-rcd (record (x 1) (y 2)))
#              (lookup (extend my-first-rcd y @) idLookingFor)))
#  ') is set(["my-first-rcd", "my-second-rcd"])
#  ##
#  # Test-withE
#  parse-and-calculate-locals('
#    (with (record (x 1) (y 3)) @)
#  ') is set(["x", "y"])
#  parse-and-calculate-locals('
#    (with (record (x @) (y 3)) 
#          (+ x y))
#  ') is set([])
#  parse-and-calculate-locals('
#    (let (my-rcd (record (z 10)))
#         (with my-rcd (+ @ (lookup my-rcd z))))
#  ') is set(["my-rcd", "z"])
#  parse-and-calculate-locals('
#    (let (my-first-rcd (record (z 10)))
#         (with (record (x 9) (y 99))
#               (+ @ (lookup my-first-rcd z))))
#  ') is set(["my-first-rcd", "x", "y"])
#  parse-and-calculate-locals('
#    (let (x 100)
#         (let (my-record (record (x 1) (y 100)))
#              ((fun (a1 a2 a3) (+ a1 (- a2 a3)))
#                    (do (assign my-record (record (x 101) (y 999)))
#                        (with my-record x))
#                    (with my-record y)
#                    @)))
#  ') is set(["x", "my-record"])
#  parse-and-calculate-locals('
#    (let (x 100)
#         (let (my-record (record (x 1) (y 100)))
#              ((fun (a1 a2 a3) (+ a1 (- a2 a3)))
#                    (do (assign my-record (record (x 101) (y 999)))
#                        (with my-record @))
#                    (with my-record y)
#                    99)))
#  ') is set(["x", "my-record", "y"])
#  parse-and-calculate-locals('
#    (let (unde-rec (if 1 
#                       (record (x "x-value"))
#                       (record (y "y-value"))))
#         (with unde-rec @))
#  ') is set(["x", "y", "unde-rec"])               # underterminable for which 
#                                                  # record to use, so we have
#                                                  # to include them all
#  parse-and-calculate-locals('
#    ((let
#        (my-record (record (argX 1) (argY 10) (argZ 100)))
#        (fun (choice base)
#             (if (== choice "c1")
#                 (- base (lookup @ argX))
#                 (if (== choice "c2")
#                     (- base (lookup my-record argY))
#                     (if == choice "c3")
#                       (- base (lookup my-record argZ))
#                       ("UNKNOWN CHOICE")))))
#      "c2" 0)
#  ') is set(["my-record", "choice", "base"])
#  parse-and-calculate-locals('
#    (let (my-record (record (argX 1) (argY 10) (argZ 100)))
#         (let (fun-set-record
#                 (fun (a1 a2 a3)
#                      (record (x (- 0 a1))
#                              (y (- 0 a2))
#                              (z (- 0 a3)))))
#              (with (fun-set-record
#                       (lookup my-record argX)
#                       (lookup my-record argY)
#                       (lookup my-record argZ))
#                    (+ @ (+ y z)))))
#  ') is set(["my-record", "fun-set-record"])
  parse-and-calculate-locals('
    (let (my-record (record (argX 1) (argY 10) (argZ 100)))
         (let (fun-set-record
                 (fun (a1 a2 a3)
                      (record (x (- 0 a1))
                              (y (- 0 a2))
                              (z (- 0 a3)))))
              (with my-record
                    (+ @ (+ y z)))))
  ') is set(["my-record", "fun-set-record", "argX", "argY", "argZ"])

                   


end
