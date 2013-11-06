#lang pyret/whalesong

data Type:
  | numT
  | strT
  | funT(params :: List<Type>, result :: Type)
  | recordT(fields :: List<FieldType>)
end

data FieldType:
  | fieldT(name :: String, type :: Type)
end

data Expr:
  | idE(name :: String)
  | numE(value :: Number)
  | strE(value :: String)
  | bopE(op :: Operator, left :: Expr, right :: Expr)
  | cifE(cond :: Expr, consq :: Expr, altern :: Expr)
  | letE(bind :: Binding, expr :: Expr, body :: Expr)
  | lamE(params :: List<Binding>, body :: Expr)
  | appE(func :: Expr, args :: List<Expr>)
  | assignE(name :: String, expr :: Expr)
  | doE(exprs :: List<Expr>)
  | recordE(fields :: List<Field>)
  | lookupE(rec :: Expr, field-name :: String)
  | extendE(rec :: Expr, field-name :: String, new-value :: Expr)

  | withE(namespace :: Expr, type :: Type, body :: Expr)
  | holeE
end

data Binding:
  | binding(name :: String, type :: Type)
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
  fun convert-binding(sexpr):
    when sexpr.get(1) <> ":":
      raise("parse - invalid binding: " + sexpr.tostring())
    end
        binding(sexpr.get(0), convert-type(sexpr.get(2)))
  end
  fun convert-type(sexpr):
    if sexpr == "num":
      numT
    else if sexpr == "str":
      strT
    else if sexpr.get(0) == "record":
      recordT(map(convert-field-type, sexpr.rest))
    else if sexpr.get(sexpr.length() - 2) == "->":
      funT(map(convert-type, sexpr.take(sexpr.length() - 2)),
                   convert-type(sexpr.last()))
    end
  end
  fun convert-field-type(sexpr):
        fieldT(sexpr.get(0), convert-type(sexpr.get(1)))
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
        letE(convert-binding(sexpr.get(1).get(0)),
             convert(sexpr.get(1).get(1)),
             convert(sexpr.get(2)))
      else if head == "with":
        withE(convert(sexpr.get(1)),
                      convert-type(sexpr.get(2)),
              convert(sexpr.get(3)))
      else if head == "record":
        recordE(map(convert-field, sexpr.rest))
      else if head == "lookup":
        lookupE(convert(sexpr.get(1)), sexpr.get(2))
      else if head == "extend":
        extendE(convert(sexpr.get(1)),
                sexpr.get(2),
                convert(sexpr.get(3)))
      else if head == "assign":
        assignE(sexpr.get(1), convert(sexpr.get(2)))
      else if head == "do":
        when is-empty(sexpr.rest):
          raise("Paret: do blocks cannot be empty")
        end
        doE(map(convert, sexpr.rest))
      else if head == "fun":
        lamE(map(convert-binding, sexpr.get(1)), convert(sexpr.get(2)))
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
  fun scan-expr(se :: Expr, possible-ids :: Set<String>) -> Set<String>:
    cases (Expr) se:
      | holeE =>
        possible-ids
      | numE(n) =>
        set([])
      | strE(s) =>
        set([])
      | idE(s) =>
        set([])
      | cifE(c, sq, alt) =>
        cr = scan-expr(c, possible-ids)
        sr = scan-expr(sq, possible-ids)
        ar = scan-expr(alt, possible-ids)
        cr.union(sr).union(ar)
      | lamE(p-l, body) =>
        
      | recordE(f-l) =>
        for fold(res from set([]), fie from f-l):
          res.union(scan-expr(fie, possible-ids))
        end
    end
  end
  scan-expr(expr, set([]))
where:
  fun check-base-case()
    parse-and-calculate-locals('
      0
    ') is set([])
    parse-and-calculate-locals('
      "hi"
    ') is set([])
    parse-and-calculate-locals('
      @
    ') is set([])
    parse-and-calculate-locals('
      (== "str" @)
    ') is set([])
    parse-and-calculate-locals('
      (== @ "str")
    ') is set([])
    parse-and-calculate-locals('
      (+ 1 @)
    ') is set([])
    parse-and-calculate-locals('
      (+ @ 1)
    ') is set([])
    parse-and-calculate-locals('
      (++ @ "second str")
    ') is set([])
    parse-and-calculate-locals('
      (++ "first str" @)
    ') is set([])
    parse-and-calculate-locals('
      (record (x @))
    ') is set([])
    parse-and-calculate-locals('
      (record (@ 9))
    ') is set([])
    parse-and-calculate-locals('
      (record (x 1) (y @))
    ') is set([])
    parse-and-calculate-locals('
      (record (x 1) (@ y))
    ') is set([])
    parse-and-calculate-locals('
      (fun ((x : num)) 3)
    ') is set([])
    parse-and-calculate-locals('
      (fun ((x : num)) @)
    ') is set(["x"])
    parse-and-calculate-locals('
      (fun ((x : num) (y : str)) @)
    ') is set(["x", "y"])
    parse-and-calculate-locals('
      (fun ((@ : num)) 99)
    ') is set([])
    parse-and-calculate-locals('
      (fun ((x : num) (@ : num) 99))
    ') is set([])
  end
  fun check-record-related():
    fun check-record-with-lookup():
      parse-and-calculate-locals('
        ((fun ((record-parm : (record (x num))))
              @)
        (record (x 99)))
      ') is set(["record-parm"])
      parse-and-calculate-locals('
        (lookup (record (x 10) (y "hello")) @)
      ') is set(["x", "y"])
      parse-and-calculate-locals('
        (lookup (record (x 10) (@ "hello")) x)
      ') is set([])
      parse-and-calculate-locals('
        (lookup (record (@ 10) (y "hello")) y)
      ') is set([])
      parse-and-calculate-locals('
        (lookup (extend (record (x 10) (y "hello")) z 99) @)
      ') is set(["x", "y", "z"])
      parse-and-calculate-locals('
        (lookup (extend (record (x 10) (@ "hello")) z 99) z)
      ') is set([])
      parse-and-calculate-locals('
        (lookup (extend (record (x 10) (y "hello")) @ 99) y)
      ') is set(["x", "y"])
    end
    fun check-record-as-parameter():
      parse-and-calculate-locals('
        ((fun ((record-parm : (record (@ num))))
             "result-string")
         (record (x 12)))
      ') is set([])
      parse-and-calculate-locals('
        ((fun ((record-parm : (record (@ num) (y num))))
             "result-string")
         (record (x 12) (y 9)))
      ') is set([])
      parse-and-calculate-locals('
        ((fun ((record-parm : (record (x num) (@ num))))
             "result-string")
         (record (x 12) (y 9)))
      ') is set([])
      parse-and-calculate-locals('
        ((fun ((record-parm : (record (x num) (y num))))
              @)
         (record (x 12) (y 9)))
      ') is set(["record-parm"])
    end
    fun check-record-as-argument():
      parse-and-calculate-locals('
        ((fun ((record-parm : (record (x num) (y num))))
             "result-string")
         (record (@ 9) (y 99)))
      ') is set([])
      parse-and-calculate-locals('
        ((fun ((record-parm : (record (x num) (y num))))
             "result-string")
         (record (x 9) (@ 99)))
      ') is set([])
    end
    fun check-record-nested-record():
      parse-and-calculate-locals('
        (lookup (record (x 10)
                        (nested-rec-field (record (y "nested-rec-fvalue"))))
         @)
      ') is set(["x", "nested-rec-field"])
      parse-and-calculate-locals('
        (lookup (record (x 10)
                        (nested-rec-field (record (@ "nested-rec-fvalue"))))
         "dummy-return-string")
      ') is set([])

    end
    fun check-record-with-with():
      parse-and-calculate-locals('
        (with (record (x 9)) (record (x num))
              @)
      ') is set(["x"])
      parse-and-calculate-locals('
        (with (record (x 9) (y "hello-y")) (record (x num) (y str))
              @)
      ') is set(["x", "y"])
    end
    check-record-with-lookup()
    check-record-as-parameter()
    check-record-as-argument()
    check-record-with-with()
    check-record-nested-record()
  end
  fun check-lambda-related():
    fun check-lambda-basic():
      parse-and-calculate-locals('
        (fun ((@ : num)) 3)
      ') is set([])
      parse-and-calculate-locals('
        (fun ((x : num) (y : str) (@ : str)) 3)
      ') is set([])
      parse-and-calculate-locals('
        (fun ((x : num)) @)
      ') is set(["x"])
      parse-and-calculate-locals('
        (fun ((x : num)) @)
      ') is set(["x"])
      parse-and-calculate-locals('
        (fun ((x : num) (y : str))
             @)
      ') is set(["x", "y"])
      parse-and-calculate-locals('
        (fun ((fun-parm : num -> num))
             @)
      ') is set(["fun-parm"])
    end
    fun check-labmda-basic-record():
      parse-and-calculate-locals('
        (fun ((fun-parm : num -> num) (rec-parm : (record (x num) (y num))))
             @)
      ') is set(["fun-parm", "rec-parm"])
      parse-and-calculate-locals('
        (fun ((rec-parm : (record (x num) (y num))) (fun-parm : num -> num))
             @)
      ') is set(["fun-parm", "rec-parm"])
      parse-and-calculate-locals('
        (fun ((rec-parm : (record (@ num) (y num))) (fun-parm : num -> num))
             fun-parm)
      ') is set([])
      parse-and-calculate-locals('
        (fun ((fun-parm : num -> num) (rec-parm : (record (@ num) (y num))))
             (lookup rec-parm y))
      ') is set([])
    end
    fun check-lambda-nested-lambda-shadowing-record():
      parse-and-calculate-locals('
        (fun ((fun-parm : num -> num) (rec-parm : (record (x num) (y num))))
             (fun ((fun-parm : num str str -> num))
                  @))
      ') is set(["fun-parm", "rec-parm"])
      parse-and-calculate-locals('
      parse-and-calculate-locals('
        (fun ((fun-parm : num -> num) (rec-parm : (record (x num) (y num))))
             (fun ((fun-parm : num str str -> num))
                  (lookup @ y)))
      ') is set(["rec-parm"])
      parse-and-calculate-locals('
        (fun ((fun-parm : num -> num) (rec-parm : (record (x num) (y num))))
             (fun ((rec-parm : (record (shadow-x num) (shadow-y num))))
                  (lookup rec-parm @)))
      ') is set(["shadow-x", "shadow-y"])
      parse-and-calculate-locals('
        (fun ((fun-parm : num -> num) (rec-parm : (record (x num) (y num))))
             (fun ((rec-parm : (record (shadow-x num) (shadow-y num))))
                  (lookup (extend rec-parm new-z "hello-value") @)))
      ') is set(["shadow-x", "shadow-y", "new-z"])
    end
    check-lambda-basic()
    check-labmda-basic-record()
    check-lambda-nested-lambda-shadowing-record()
  end

end
