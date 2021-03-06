package simplifierProven.GUERIN

import library._

object String {

abstract sealed class char
final case class
  Char(a: Boolean, b: Boolean, c: Boolean, d: Boolean, e: Boolean, f: Boolean,
        g: Boolean, h: Boolean)
  extends char

} /* object String */
class MySimplifier extends Simplifier{

  def simplify(x0: List[Symbol]): List[Symbol] = x0 match {
    case Nil => Nil
    case List(Star) => List(Star)
    case List(Qmark) => List(Qmark)
    case List(Plus) => List(Plus)
    case List(Char(a)) => List(Char(a))
    case Char(a) :: v :: va => Char(a) :: simplify(v :: va)
    case Star :: Char(a) :: m => Star :: Char(a) :: simplify(m)
    case Qmark :: Char(a) :: m => Qmark :: Char(a) :: simplify(m)
    case Plus :: Char(a) :: m => Plus :: Char(a) :: simplify(m)
    case Star :: Star :: m => Star :: simplify(m)
    case Star :: Qmark :: m => Plus :: simplify(m)
    case Star :: Plus :: m => Plus :: simplify(m)
    case Qmark :: Star :: m => Plus :: simplify(m)
    case Qmark :: Qmark :: m => Qmark :: Qmark :: simplify(m)
    case Qmark :: Plus :: m => Qmark :: Plus :: simplify(m)
    case Plus :: Star :: m => Plus :: simplify(m)
    case Plus :: Qmark :: m => Plus :: Qmark :: simplify(m)
    case Plus :: Plus :: m => Plus :: Plus :: simplify(m)
  }

}
