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
  fun check-base-case():
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
      (fun ((x : num) (@ : num)) 99)
    ') is set([])
  end
  fun check-record():
    fun check-record-lookup():
      fun check-record-lookup-nested():
        parse-and-calculate-locals('
          (lookup (record (x 10)
                          (y-nested (record (z-nested-nested "z-nested-nested-value"))))
           @)
        ') is set(["x", "y-nested", "z-nested-nested"])
        parse-and-calculate-locals('
          (lookup (record (x 10)
                          (y-nested (record (@ "z-nested-nested-value"))))
           y-nested)
        ') is set([])
        parse-and-calculate-locals('
          (lookup (record (x 10)
                          (y (extend (record (z-nested "z-nested-value"))
                                     m-nested-nested
                                     "m-nested-nested-value")))
           @)
        ') is set(["x", "y", "z-nested", "m-nested-nested"])
        parse-and-calculate-locals('
          (lookup (record (x 10)
                          (y (extend (record (@ "z-nested-nested-value"))
                                     m-nested
                                     "m-nested-value")))
                  m-nested)
        ') is set([])
      end
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
      ') is set([])
      check-record-lookup-nested()
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
    fun check-record-with-with():
      parse-and-calculate-locals('
        (with (record (x 9))
              (record (x num))
              @)
      ') is set(["x"])
      parse-and-calculate-locals('
        (with (record (x 9) (y "hello-y"))
              (record (x num) (y str))
              @)
      ') is set(["x", "y"])
      parse-and-calculate-locals('
        (with (record (x 9) (y-nested (record (z-nested-nested "z-nested-nested-value"))))
              (record (x num) (y-nested (record (z-nested-nested str))))
              @)
      ') is set(["x", "y-nested", "z-nested-nested"])
      parse-and-calculate-locals('
        (with (record (x 9) (y-nested (extend (record (z-nested-nested "z-nested-nested-value"))
                                              m-nested-nested-nested
                                              "m-nested-nested-nested-value")))
              (record (x num) (y-nested (record (z-nested-nested str) (m-nested-nested-nested str))))
              @)
      ') is set(["x", "y-nested", "z-nested-nested", "m-nested-nested-nested"])
    end
    check-record-lookup()
    check-record-as-parameter()
    check-record-as-argument()
    check-record-with-with()
  end
  fun check-lambda():
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
        (fun ((x : num) (y : str))
             @)
      ') is set(["x", "y"])
      parse-and-calculate-locals('
        (fun ((fun-parm : num -> num))
             @)
      ') is set(["fun-parm"])
    end
    fun check-lambda-record():
      fun check-lambda-record-nested():
        parse-and-calculate-locals('
          (fun ((fun-parm : num -> num) (rec-parm : (record (x num) (y num))))
               (fun ((fun-parm : num str str -> num))
                    @))
        ') is set(["fun-parm", "rec-parm"])
        parse-and-calculate-locals('
          (fun ((fun-parm : num -> num) (rec-parm : (record (x num) (y num))))
               (fun ((fun-parm : num str str -> num))
                    (lookup @ y)))
        ') is set(["fun-parm", "rec-parm"])
        parse-and-calculate-locals('
          (fun ((fun-parm : num -> num) (rec-parm : (record (x num) (y num))))
               (fun ((rec-parm : (record (x-shadowed num) (y-shadowed num))))
                    (lookup rec-parm @)))
        ') is set(["x-shadowed", "y-shadowed"])
        parse-and-calculate-locals('
          (fun ((fun-parm : num -> num) (rec-parm : (record (x num) (y num))))
               (fun ((rec-parm : (record (x-shadowed num) (y-shadowed num))))
                    (lookup (extend rec-parm z "hello-value") @)))
        ') is set(["x-shadowed", "y-shadowed", "z"])
      end
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
      check-lambda-record-nested()
    end
    check-lambda-basic()
    check-lambda-record()
  end
  fun check-cif():
    parse-and-calculate-locals('
      (if 1
          @
          "false-branch")
    ') is set([])
    parse-and-calculate-locals('
      (if 0
          "true-branch"
          @)
    ') is set([])
    parse-and-calculate-locals('
      (if 0
          "true-branch"
          @)
    ') is set([])
    parse-and-calculate-locals('
      ((fun ((x : str) (y : str))
            (if (== x y)
                @
                0))
             "x-arg-value" "y-arg-value")
    ') is set(["x", "y"])
    parse-and-calculate-locals('
      ((fun ((x : str) (y : str))
            (if (== x y)
                (fun ((x-nested-left : num) (y-nested-left : num))
                     (+ x-nested-left @))
                (fun ((x-nested-right : num) (y-nested-right : num))
                     (* x-nested-right y-nested-right))))
             "x-arg-value" "y-arg-value")
    ') is set(["x", "y", "x-nested-left", "y-nested-left"])
    parse-and-calculate-locals('
      (with ((fun ((x : str) (y : str))
                  (if (== x y)
                      (record (m "m-left-value"))
                      (record (m "m-right-value"))))
              "x-value" "y-value")
            (record (m str))
            @)
    ') is set(["m"])
    parse-and-calculate-locals('
      (with ((fun ((x : num) (y : num))
                  (if (- x y)
                      (if (+ x 1)
                          (record (m "m-left-l-value"))
                          (record (m "m-left-r-value")))
                      (record (m "m-right-value"))))
              "x-value" "y-value")
            (record  (m str))
            @)
    ') is set(["m"])
  end
  fun check-let():
    parse-and-calculate-locals('
      (let ((x : num) 99)
           @)
    ') is set(["x"])
    parse-and-calculate-locals('
      (let ((x : num) 9)
           ((fun ((x : str)) @) "cover you"))
    ') is set(["x"])
    parse-and-calculate-locals('
      (let ((my-rec : (record (x str) (y str)))
            (record (x "x-value") (y "y-value") (z-unused "z-unused-value")))
           (with my-rec
                 (record (x str) (y str))
                 @))
    ') is set["x", "y", "my-rec"]
    parse-and-calculate-locals('
      (let ((my-rec : (record (x str) (y str)))
            (record (x "x-value") (y "y-value") (z-unused "z-unused-value")))
           (with @
                 (record (x str) (y str))
                 "do-nothing"))
    ') is set["my-rec"]
    parse-and-calculate-locals('
      (let ((my-rec : (record (x str) (y str)))
            (record (x "x-value") (y "y-value") (z-unused @)))
           (with my-rec
                 (record (x str) (y str))
                 "do-nothing"))
    ') is set[]
    parse-and-calculate-locals('
      (let ((my-rec : (record (x str) (y str)))
            (record (x "x-value") (y "y-value") (z-unused "z-unused-value")))
           (with my-rec
                 (record (x str) (y str))
                 (extend my-rec @ "random-value")))
    ') is set["my-rec"]                           # for extend or create a new record,
                                                  # the id-hole could be filled by
                                                  # any identifier in the id-env
    parse-and-calculate-locals('
      (let ((my-rec : (record (x str) (y str)))
            (record (x "x-value") (y "y-value") (z-unused "z-unused-value")))
           (with my-rec
                 (record (x str) (y str))
                 (do (assign my-rec (extend my-rec z "z-value"))
                     (with my-rec
                           (record (x str) (y str) (z str))
                           @))))
    ') is set["my-rec", "x", "y", "z"]            # after several times of supplementing
                                                  # the scope, no duplicate id occurs
  end
  fun check-do():
    parse-and-calculate-locals('
      (do 3 "string" @)
    ') is set[]
    parse-and-calculate-locals('
      (do @ "string" 99)
    ') is set[]
    parse-and-calculate-locals('
      (let ((my-rec : (record (x str))) (record (x "x-value")))
           (do (assign my-rec 
                       (record (x "x-new-value")
                               (y-extra "y-extra-value")))
               (with my-rec 
                     (record (x str)
                             (y-extra str))        # as my-rec has been type updated,
                                                   # the record scope should be just
                                                   # stick with the new type
                     @)))
    ') is set["my-rec", "x", "y-extra"]
    parse-and-calculate-locals('
      (let ((my-rec : (record (x str))) (record (x "x-value")))
           (do (assign my-rec 
                       (record (x "x-new-value")
                               (y-extra "y-extra-value")))
               (with my-rec 
                     (record (x str)
                             (y-extra str))
                     (assign my-rec
                             (record (x "x-new-new-value")
                                     (y-extra @))))))
    ') is set["my-rec", "x", "y-extra"]            # if chosen "y-extra", the new "y-extra"
                                                   # identifier would just refer to itself
    parse-and-calculate-locals('
      (let ((my-rec : (record (x str))) (record (x "x-value")))
           (do (assign my-rec 
                       (record (x "x-new-value")
                               (y-extra "y-extra-value")))
               (lookup my-rec @)))                 # id-env shouldn't be taken into
                                                   # account in this case, because
                                                   # it is unbound to the record "my-rec"
    ') is set["x", "y-extra"]
  end
  fun check-assign():
    parse-and-calculate-locals('
      (let ((x : num) 9)
           (assign @ 77))
    ') is set["x"]
    parse-and-calculate-locals('
      (let ((x : num) 9)
           (assign x @))
    ') is set["x"]
    parse-and-calculate-locals('
      (lookup (let ((my-record : (record (x str))) (record (x "x-value")))
                   (assign my-record
                           (record (x "x-new-value")
                                   (y-extra "y-extra-value"))))
              @)
    ') is set["x", "y-extra"]
    parse-and-calculate-locals('
      (lookup (let ((my-record : (record (x str))) (record (x "x-value")))
                   (assign my-record
                           (record (x "x-new-value")
                                   (@ "random-value"))))
              x)
    ') is set[]
    parse-and-calculate-locals('
      (lookup (let ((my-record : (record (x str))) (record (x "x-value")))
                   (assign my-record
                           (record (x "x-new-value")
                                   (y-extra @))))
              y-extra)
    ') is set["my-record"]                        # this could form a recursive data
                                                  # y-extra : my-record -> my-record
                                                  # (which contains y-extra)
  end
  check-base-case()
  check-record()
  check-lambda()
  check-cif()
  check-let()
  check-do()
  check-assign()
end
