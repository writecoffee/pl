
getloc = fun(): gensym("id") end

fun rec-lookup(field-name :: String, rec-fields :: List<FieldV>) -> Value:
  cases(List) rec-fields:
    | empty => raise("Field not Found in record:" + field-name)
    | link(first, rest) => 
        if first.name == field-name:
          first.value
        else:
          rec-lookup(field-name, rest)
        end
  end
end


fun lookup-env(name-id :: String, env :: Env, store :: Store) -> String:
  cases(Env) env:
    | mt-env => raise("Unbound identifier: " + name-id)
    | an-env(name, loc, rest-env) =>
        if name == name-id:
          loc
        else:
          lookup-env(name-id, rest-env, store)
        end
  end
end


fun fetch(loc-id :: String, store :: Store) -> Value:
  cases(Store) store:
    | mt-store => raise("Something went VERY wrong")
    | a-store(loc, val, rest-store) =>
        if loc-id == loc:
          val
        else:
          fetch(loc-id, rest-store)
        end
  end
end

fun shelve(loc-id :: String, item-val :: Value, store :: Store) -> Store:
  cases(Store) store:
    | mt-store => raise("Something went VERY wrong")
    | a-store(loc, val, rest-store) =>
        if loc-id == loc:
          a-store(loc, item-val, rest-store)
        else:
          a-store(loc, val, shelve(loc-id, item-val, rest-store))
        end
  end
end


fun weft(args :: List<Expr>, arg-env :: Env, store :: Store) -> List<Result>:
  cases(List) args:
    | empty => empty
    | link(first, rest) =>
        cur-arg = interp-full(first, arg-env, store)
        link(cur-arg, weft(rest, arg-env, cur-arg.store))
  end
end

fun apply(params :: List<String>, args :: List<Result>, body :: Expr, cl-env :: Env, store :: Store) -> Result:
  new-locations = map(fun(x): getloc() end, args)
  interp-full(body, fold2(fun(clos-env, param-name, new-loc):
                            an-env(param-name, new-loc, clos-env)
                          end, cl-env, params, new-locations),
                    fold2(fun(cl-store, new-loc, arg-val):
                            a-store(new-loc, arg-val.val, cl-store)
                          end, store, new-locations, args))
end

fun binOp(binop :: Operator, left :: Expr, right :: Expr, env :: Env, store :: Store) -> Result:
  cases(Result) interp-full(left, env, store):
    | result(left-val, left-store) =>
        cases(Value) left-val:
          | numV(l-value) =>
              cases(Result) interp-full(right, env, left-store):
                | result(right-val, right-store) =>
                    cases(Value) right-val:
                      | numV(r-value) => 
                          cases(Operator) binop:
                            | plus => result(numV(l-value + r-value), right-store)
                            | minus => result(numV(l-value - r-value), right-store)
                            | else => raise("Invalid operator for numbers")
                          end
                      | else => raise("Argument mismatch: both args must be of the same type")
                    end
              end
          | strV(l-value) =>
              cases(Result) interp-full(right, env, left-store):
                | result(right-val, right-store) =>
                    cases(Value) right-val:
                      | strV(r-value) =>
                          cases(Operator) binop:
                              | append => result(strV(l-value + r-value), right-store)
                              | str-eq => result(numV(if l-value == r-value: 1 else: 0 end), right-store)
                              | else => raise("Invalid operator for strings")
                          end
                      | else => raise("Argument mismatch: both args must be of the same type")
                    end
              end
          | else => raise("Invalid argument for binary op")
        end
  end
end
fun interp-full(prog :: Expr, env :: Env, store :: Store) -> Result:
  cases(Expr) prog:
    | idE(name) => result(fetch(lookup-env(name, env, store), store), store)
    | numE(value) => result(numV(value), store)
    | strE(value) => result(strV(value), store)
    | bopE(op, left, right) => binOp(op, left, right, env, store)
    | cifE(cond, consq, altern) =>
        cases(Result) interp-full(cond, env, store):
          | result(val, cond-store) =>
              cases(Value) val:
                | numV(value) =>
                    if value <> 0:
                      interp-full(consq, env, cond-store)
                    else:
                      interp-full(altern, env, cond-store)
                    end
                | else => raise("Test condition must be a number")
              end
        end
    | letE(id-name, expr, body) =>
        new-loc = getloc()
        new-res = interp-full(expr, env, store)
        interp-full(body, an-env(id-name, new-loc, env),
                    a-store(new-loc, new-res.val, new-res.store))
    | lamE(params, body) => result(funV(params, body, env), store)
    | appE(func, args) =>
        cases(Result) interp-full(func, env, store):
          |result(cl-val, cl-store) =>
              cases(Value) cl-val:
                | funV(params, body, cl-env) =>
                    arg-res = weft(args, env, cl-store)
                    apply(params, arg-res, body, cl-env, cases(List) arg-res:
                                                          | empty => cl-store
                                                          | link(_, _) => arg-res.last().store
                                                         end)
                | else => raise("My dad's not a phone!  And you can only apply lambdas!")
              end
        end
    | assignE(name, expr) =>
        set-res = interp-full(expr, env, store)
        result(set-res.val, shelve(lookup-env(name, env, store), set-res.val, set-res.store))
    | doE(exprs) => for fold(exp-res from result(numV(0), store), list-expr from exprs):
        interp-full(list-expr, env, exp-res.store)
        end
    | recordE(fields) =>
        field-res = weft(map(fun(item): item.value end, fields), env, store)
        result(recV(map2(fun(e-name, e-val): fieldV(e-name, e-val.val) end,
                          map(fun(item): item.name end, fields),
                          field-res)),  cases(List) field-res:
                                          | empty => store
                                          | link(_, _) => field-res.last().store
                                        end)
    | lookupE(rec, field-name) =>
        lookup-res = interp-full(rec, env, store)
        cases(Value) lookup-res.val:
          | recV(fields) => result(rec-lookup(field-name, fields), lookup-res.store)
          | else => raise("Can only perform lookups on records")
        end
    | extendE(rec, field-name, new-value) =>
        extend-res = interp-full(rec, env, store)
        cases(Value) extend-res.val:
          | recV(fields) =>
              new-val-res = interp-full(new-value, env, extend-res.store)
              result(recV(link(fieldV(field-name, new-val-res.val), fields)), new-val-res.store)
          | else => raise("Can only extend records")
        end

    | withE(namespace, body) =>
        namespace-res = interp-full(namespace, env, store)
        cases(Value) namespace-res.val:
          | recV(fields) =>
              rev-fields = fields.reverse()
              locs = map(fun(_): gensym("id") end, rev-fields)
              new-env = for fold2(with-env from env, binding from rev-fields, loc from locs):
            an-env(binding.name, loc, with-env)
              end
              new-store = for fold2(with-store from namespace-res.store,
                                    loc from locs, binding from rev-fields):
                a-store(loc, binding.value, with-store)
              end
              interp-full(body, new-env, new-store)
          | else => raise("Namespace must be a record")
        end
  end

=========================================== 1
Looks good to me. All test cases passed if not taking the test for previous part 
where "((fun (x y) (+ x y)) 3 7 9)" displays a arity mismatch uncaught.

Applied a lot of fancy build-in functions, that's great! The identation could be
much better if you could limit the line max length and use two spaces as indent.

=========================================== 2

Looks good to me for the with and record part. But there might be legacy issue
on the interp on let part. The following test case yield 

Test eval("
    ((let (x 1)
          (fun (y) (+ x y))) 5)
      ") is numV(6) raised an error:
invalid location: stloc_111431

And hence cannot sustain more complicated test cases.

Consistent identation and clear seperatation of the function responsbilities.


=========================================== 3

Looks good to me for the with and record part. But there might be legacy issue
on the interp on let part. The following test case yield 

Test eval("
    ((let (x 1)
          (fun (y) (+ x y))) 5)
      ") is numV(6) raised an error:
invalid location: stloc_111431

And hence cannot sustain more complicated test cases.

