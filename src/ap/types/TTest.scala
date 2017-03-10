package ap.types

import ap.parser._
import ap.SimpleAPI

object TTest extends App {

  val p = SimpleAPI(genTotalityAxioms = true)
  import p._
  import IExpression._

  println("Starting")

  val x = createConstant("x")
  val y = createConstant("y")
  val z = createConstant("z", Sort.Nat)
  val a = createConstant("a", 0 until 100)

  scope {
    val f = ex((a, b) => a === x + b)
    println(pp(f))
    !! (f)
    println(???)
  }

  scope {
    val f = Sort.Nat ex (_ === x)
    println(pp(f))
    !! (f)
    println(???)
  }

  scope {
    val f = Sort.Nat all { a => x === a }
    println(pp(f))
    !! (f)
    println(???)
  }

  scope {
    val f = (Sort.Nat ex { a => x === y + a }) <===> (y <= x)
    println(pp(f))
    ?? (f)
    println(???)
  }

  scope {
    val f = ((0 until 10) ex (_ > x))
    val g = ((0 to 9) ex (_ > x))
    println(pp(f))
    println(pp(g))
    println(pp(simplify(f)))
    ?? (f <===> g)
    println(???)
  }

  scope {
    !! (z < -10)
    println(???)
  }

  scope {
    val x1 = createConstant("x1", 0 until 10)
    val x2 = createConstant("x2", 10 until 20)
    scope {
      println(pp(x1 === x2))
      !! (x1 === x2)
      println(???)
    }
    scope {
      ?? (x2 > x1)
      println(???)
    }
  }

  scope {
    val X = createExistentialConstant("X", Sort.Nat)
    ?? (X > 10 & 2*X < 30)
    println(???)
    println(pp(getMinimisedConstraint))
  }

  scope {
    val c = createConstant(10 until 20)
    !! (c**c < 10000)
    println(???)
    println(eval(c))
    !! (c**c > 1000)
    println(???)
  }

  scope {
    val f = createFunction("f", List(Sort.Nat), 0 until 10)
    scope {
      !! (f(z) > 100)
      println(???)
    }
    scope {
      !! (Sort.Nat all { x => trig(f(x+1) > f(x), f(x)) })
//      !! (f(15) === x)
      println(???)
    }
  }

  p.shutDown

  println("Finished")

}