#lang pyret

provide *

import format as F

fix-width = F.fix-width
format = F.format

data Expr:
  | numE(val :: Number)
  | plusE(left :: Expr, right :: Expr)
  | idE(name :: String)
  | cifE(cond :: Expr, consq :: Expr, altern :: Expr)
  | letE(name :: String, expr :: Expr, body :: Expr)
  | lamE(param :: String, body :: Expr)
  | appE(func :: Expr, arg :: Expr)
  | doE(stmts :: List<Expr>)
  | pairE(left :: Expr, right :: Expr)
  | leftE(pair :: Expr)
  | rightE(pair :: Expr)
  | setLeftE(pair :: Expr, new-val :: Expr)
  | setRightE(pair :: Expr, new-val :: Expr)
  | gcE(expr :: Expr)
end

data Cell:
  | strC(val :: String)
  | numC(val :: Number)
  | exprC(val :: Expr)
end

Loc = Number

data Box<a>:
  | box(mutable v)
end

data Bind:
  | bind(name :: String, loc :: Box<Loc>)
end

data Env:
  | env(bindings :: List<Bind>, temporaries :: List<Box<Loc>>)
end

data Result:
  | result(loc :: Loc, runtime :: Runtime)
end

data Runtime:
  | runtime(memory :: Array,
            mutable offset :: Number,
            mutable front-half :: Boolean)
end

fun make-runtime(size :: Number):
  runtime(array-of(0, size), 0, true)
end

fun parse(sexpr) -> Expr:
  if List(sexpr):
    head = sexpr.first
    if head == "+":
      plusE(parse(sexpr.get(1)),
            parse(sexpr.get(2)))
    else if head == "if":
      cifE(parse(sexpr.get(1)),
           parse(sexpr.get(2)),
           parse(sexpr.get(3)))
    else if head == "let":
      letE(sexpr.get(1).get(0),
           parse(sexpr.get(1).get(1)),
           parse(sexpr.get(2)))
    else if head == "fun":
      lamE(sexpr.get(1).get(0), parse(sexpr.get(2)))
    else if head == "do":
      doE(map(parse, sexpr.rest))
    else if head == "pair":
      pairE(parse(sexpr.get(1)), parse(sexpr.get(2)))
    else if head == "left":
      leftE(parse(sexpr.get(1)))
    else if head == "right":
      rightE(parse(sexpr.get(1)))
    else if head == "set-left":
      setLeftE(parse(sexpr.get(1)), parse(sexpr.get(2)))
    else if head == "set-right":
      setRightE(parse(sexpr.get(1)), parse(sexpr.get(2)))
    else if head == "gc":
      gcE(parse(sexpr.get(1)))
    else:
      func = parse(head)
      arg = parse(sexpr.get(1))
      appE(func, arg)
    end
  else if Number(sexpr):
    numE(sexpr)
  else if String(sexpr):
    idE(sexpr)
  end
end


fun print-heap(r :: Runtime):
  EXPR-STR = "<expr>"
  BASE = 10
  COL-HEADER-WIDTH = 5
  COL-WIDTH = 10

  length = r.memory.length()
  rows = (length / BASE).floor()
  trailing = length.modulo(BASE)

  header = [fix-width(" ", COL-HEADER-WIDTH)] +
           range(0, BASE).map(fun(i): fix-width(torepr(i), COL-WIDTH);)

  fun build-str(l, s): for fold(ss from "", i from range(0, l)): ss + s;;

  header-line = [build-str(COL-HEADER-WIDTH, " ")] +
                range(0, BASE).map(fun(i): build-str(COL-WIDTH, "-");)

  fun serialize-contents(v):
    s = if Expr(v): "<expr>" else: v._torepr();
    fix-width(s, COL-WIDTH)
  end

  fun mk-col(i): fix-width((i * BASE)._torepr(), COL-HEADER-WIDTH - 1) + "|";

  info = format("~a is live, offset is ~a",
    [if r!front-half: "front" else: "back";, r!offset])

  init = info + "\n" + header.join-str(" ") + "\n" +
         header-line.join-str("-") + "\n"
  all-but-trailing = for fold(str from init, i from range(0, rows)):
    format-pieces = [mk-col(i)] + range(0, BASE).map(fun(_): "~a";)
    format-values = for map(j from range(0, BASE)):
      serialize-contents(r.memory.get((BASE * i) + j))
    end
    format-str = format(format-pieces.join-str(" "), format-values)
    str + format-str + "\n"
  end

  trailing-pieces = [mk-col(rows)] + range(0, trailing).map(fun(_): "~a";)
  trailing-values = range(0, trailing).map(fun(i):
      serialize-contents(r.memory.get((BASE * rows) + i));)

  trailing-str = format(trailing-pieces.join-str(" "), trailing-values)

  all-but-trailing + trailing-str + "\n"
end

