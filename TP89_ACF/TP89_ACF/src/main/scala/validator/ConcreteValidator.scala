package validator.GUERIN

import bank._
import validator.GUERIN.tp89.etat


// Automatic conversion of bank.message to tp89.messages and Nat to bank.Nat
object Converter{
  implicit def bank2message(m:bank.message):tp89.message=
    m match {
    case bank.Pay((bank.Nat.Nata(c),(bank.Nat.Nata(m),bank.Nat.Nata(i))),bank.Nat.Nata(p)) => tp89.Pay((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(i))),Nat.Nata(p))
    case bank.Ack((bank.Nat.Nata(c),(bank.Nat.Nata(m),bank.Nat.Nata(i))),bank.Nat.Nata(p)) => tp89.Ack((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(i))),Nat.Nata(p))
    case bank.Cancel((bank.Nat.Nata(c),(bank.Nat.Nata(m),bank.Nat.Nata(i)))) => tp89.Cancel((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(i))))
  }
  
  implicit def trans2bankTrans(l:List[((Nat.nat,(Nat.nat,Nat.nat)),Nat.nat)]): List[((bank.Nat.nat,(bank.Nat.nat,bank.Nat.nat)),bank.Nat.nat)]=
    l match {
    case Nil => Nil
    case ((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(i))),Nat.Nata(p))::r => ((bank.Nat.Nata(c),(bank.Nat.Nata(m),bank.Nat.Nata(i))),bank.Nat.Nata(p))::trans2bankTrans(r)
  }
}

import Converter._


/* The object to complete */
class ConcreteValidator extends TransValidator{
  var t : List[((Nat.nat, (Nat.nat, Nat.nat)),
    (table.option[Nat.nat],
      (table.option[Nat.nat], tp89.etat)))] = List.empty
  // TODO
  def process(m:message):Unit={ t = tp89.traiterMessage(m,t)}

  // TODO
  def getValidTrans= tp89.export2(t);
}
object HOL {

trait equal[A] {
  val `HOL.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)
object equal {
  implicit def `Product_Type.equal_prod`[A : equal, B : equal]: equal[(A, B)] =
    new equal[(A, B)] {
      val `HOL.equal` = (a: (A, B), b: (A, B)) =>
        Product_Type.equal_proda[A, B](a, b)
    }
  implicit def `Nat.equal_nat`: equal[Nat.nat] = new equal[Nat.nat] {
    val `HOL.equal` = (a: Nat.nat, b: Nat.nat) => Nat.equal_nata(a, b)
  }
}

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

} /* object HOL */

object Code_Numeral {

  def integer_of_nat(x0: Nat.nat): BigInt = x0 match {
    case Nat.Nata(x) => x
  }

} /* object Code_Numeral */

object Nat {

  abstract sealed class nat
  final case class Nata(a: BigInt) extends nat

  def equal_nata(m: nat, n: nat): Boolean =
    Code_Numeral.integer_of_nat(m) == Code_Numeral.integer_of_nat(n)

  def less_nat(m: nat, n: nat): Boolean =
    Code_Numeral.integer_of_nat(m) < Code_Numeral.integer_of_nat(n)

  def zero_nat: nat = Nata(BigInt(0))

} /* object Nat */

object Product_Type {

  def equal_proda[A : HOL.equal, B : HOL.equal](x0: (A, B), x1: (A, B)): Boolean =
    (x0, x1) match {
      case ((x1, x2), (y1, y2)) => HOL.eq[A](x1, y1) && HOL.eq[B](x2, y2)
    }

} /* object Product_Type */

object table {

  abstract sealed class option[A]
  final case class Somea[A](a: A) extends option[A]
  final case class Nonea[A]() extends option[A]

  def assoc[A : HOL.equal, B](uu: A, x1: List[(A, B)]): option[B] = (uu, x1) match
  {
    case (uu, Nil) => Nonea[B]()
    case (x1, (x, y) :: xs) =>
      (if (HOL.eq[A](x, x1)) Somea[B](y) else assoc[A, B](x1, xs))
  }

  def modify[A : HOL.equal, B](x: A, y: B, xa2: List[(A, B)]): List[(A, B)] =
    (x, y, xa2) match {
      case (x, y, Nil) => List((x, y))
      case (x, y, (z, u) :: r) =>
        (if (HOL.eq[A](x, z)) (x, y) :: r else (z, u) :: modify[A, B](x, y, r))
    }

  def equal_option[A : HOL.equal](x0: option[A], x1: option[A]): Boolean =
    (x0, x1) match {
      case (Somea(x1), Nonea()) => false
      case (Nonea(), Somea(x1)) => false
      case (Somea(x1), Somea(y1)) => HOL.eq[A](x1, y1)
      case (Nonea(), Nonea()) => true
    }

} /* object table */

object tp89 {

  abstract sealed class etat
  final case class valide() extends etat
  final case class progress() extends etat
  final case class annuler() extends etat

  abstract sealed class message
  final case class Pay(a: (Nat.nat, (Nat.nat, Nat.nat)), b: Nat.nat) extends
    message
  final case class Ack(a: (Nat.nat, (Nat.nat, Nat.nat)), b: Nat.nat) extends
    message
  final case class Cancel(a: (Nat.nat, (Nat.nat, Nat.nat))) extends message

  def getVal(x0: table.option[Nat.nat]): Nat.nat = x0 match {
    case table.Somea(x) => x
    case table.Nonea() => Nat.zero_nat
  }

  def equal_etat(x0: etat, x1: etat): Boolean = (x0, x1) match {
    case (progress(), annuler()) => false
    case (annuler(), progress()) => false
    case (valide(), annuler()) => false
    case (annuler(), valide()) => false
    case (valide(), progress()) => false
    case (progress(), valide()) => false
    case (annuler(), annuler()) => true
    case (progress(), progress()) => true
    case (valide(), valide()) => true
  }

  def egOptOpt(uu: table.option[Nat.nat], uv: table.option[Nat.nat]): Boolean =
    (uu, uv) match {
      case (table.Somea(x), table.Somea(y)) =>
        (if (Nat.equal_nata(x, y)) true else false)
      case (table.Nonea(), uv) => false
      case (uu, table.Nonea()) => false
    }

  def export2(x0: List[((Nat.nat, (Nat.nat, Nat.nat)),
    (table.option[Nat.nat],
      (table.option[Nat.nat], etat)))]):
  List[((Nat.nat, (Nat.nat, Nat.nat)), Nat.nat)]
  =
    x0 match {
      case Nil => Nil
      case ((c, (m, i)), (client, (marchant, e))) :: xs =>
        (if (equal_etat(e, valide()) && egOptOpt(client, marchant))
          ((c, (m, i)), getVal(client)) :: export2(xs) else export2(xs))
    }

  def egOptNat(x0: table.option[Nat.nat], y: Nat.nat): Boolean = (x0, y) match {
    case (table.Somea(x), y) => (if (Nat.equal_nata(x, y)) true else false)
    case (table.Nonea(), uv) => false
  }

  def infOptNat(x0: table.option[Nat.nat], y: Nat.nat): Boolean = (x0, y) match {
    case (table.Somea(x), y) => (if (Nat.less_nat(y, x)) true else false)
    case (table.Nonea(), uv) => false
  }

  def supOptNat(x0: table.option[Nat.nat], y: Nat.nat): Boolean = (x0, y) match {
    case (table.Somea(x), y) => (if (Nat.less_nat(x, y)) true else false)
    case (table.Nonea(), uv) => false
  }

  def traiterMessage(x0: message,
                     bdd: List[((Nat.nat, (Nat.nat, Nat.nat)),
                       (table.option[Nat.nat],
                         (table.option[Nat.nat], etat)))]):
  List[((Nat.nat, (Nat.nat, Nat.nat)),
    (table.option[Nat.nat], (table.option[Nat.nat], etat)))]
  =
    (x0, bdd) match {
      case (Cancel(i), bdd) =>
        (table.assoc[(Nat.nat, (Nat.nat, Nat.nat)),
          (table.option[Nat.nat],
            (table.option[Nat.nat], etat))](i, bdd)
        match {
          case table.Somea(a) =>
          {
            val (aa, b): (table.option[Nat.nat], (table.option[Nat.nat], etat)) =
              a
            val (ba, _): (table.option[Nat.nat], etat) = b;
            table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
              (table.option[Nat.nat],
                (table.option[Nat.nat],
                  etat))](i, (aa, (ba, annuler())), bdd)
          }
          case table.Nonea() => bdd
        })
      case (Pay((c, (m, i)), n), bdd) =>
        (table.assoc[(Nat.nat, (Nat.nat, Nat.nat)),
          (table.option[Nat.nat],
            (table.option[Nat.nat], etat))]((c, (m, i)), bdd)
        match {
          case table.Somea((_, (_, valide()))) => bdd
          case table.Somea((client, (marchant, progress()))) =>
            (if (supOptNat(marchant, n) &&
              (! (Nat.equal_nata(n, Nat.zero_nat)) &&
                ! (table.equal_option[Nat.nat](marchant,
                  table.Somea[Nat.nat](Nat.zero_nat)))))
              table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                (table.option[Nat.nat],
                  (table.option[Nat.nat],
                    etat))]((c, (m, i)),
                (table.Somea[Nat.nat](n),
                  (table.Somea[Nat.nat](n), valide())),
                bdd)
            else (if (egOptNat(marchant, n) &&
              (! (Nat.equal_nata(n, Nat.zero_nat)) &&
                ! (table.equal_option[Nat.nat](marchant,
                  table.Somea[Nat.nat](Nat.zero_nat)))))
              table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                (table.option[Nat.nat],
                  (table.option[Nat.nat],
                    etat))]((c, (m, i)),
                (table.Somea[Nat.nat](n), (marchant, valide())), bdd)
            else (if (supOptNat(client, n) ||
              table.equal_option[Nat.nat](client,
                table.Nonea[Nat.nat]()))
              table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                (table.option[Nat.nat],
                  (table.option[Nat.nat],
                    etat))]((c, (m, i)), (table.Somea[Nat.nat](n), (marchant, progress())), bdd)
            else bdd)))
          case table.Somea((_, (_, annuler()))) => bdd
          case table.Nonea() =>
            table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
              (table.option[Nat.nat],
                (table.option[Nat.nat],
                  etat))]((c, (m, i)),
              (table.Somea[Nat.nat](n),
                (table.Nonea[Nat.nat](), progress())),
              bdd)
        })
      case (Ack((c, (m, i)), n), bdd) =>
        (table.assoc[(Nat.nat, (Nat.nat, Nat.nat)),
          (table.option[Nat.nat],
            (table.option[Nat.nat], etat))]((c, (m, i)), bdd)
        match {
          case table.Somea((_, (_, valide()))) => bdd
          case table.Somea((client, (marchant, progress()))) =>
            (if (infOptNat(client, n) &&
              (! (Nat.equal_nata(n, Nat.zero_nat)) &&
                ! (table.equal_option[Nat.nat](client,
                  table.Somea[Nat.nat](Nat.zero_nat)))))
              table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                (table.option[Nat.nat],
                  (table.option[Nat.nat],
                    etat))]((c, (m, i)), (client, (client, valide())),
                bdd)
            else (if (egOptNat(client, n) &&
              (! (Nat.equal_nata(n, Nat.zero_nat)) &&
                ! (table.equal_option[Nat.nat](client,
                  table.Somea[Nat.nat](Nat.zero_nat)))))
              table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                (table.option[Nat.nat],
                  (table.option[Nat.nat],
                    etat))]((c, (m, i)),
                (client, (table.Somea[Nat.nat](n), valide())), bdd)
            else (if (infOptNat(marchant, n) ||
              table.equal_option[Nat.nat](marchant,
                table.Nonea[Nat.nat]()))
              table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                (table.option[Nat.nat],
                  (table.option[Nat.nat],
                    etat))]((c, (m, i)), (client, (table.Somea[Nat.nat](n), progress())), bdd)
            else bdd)))
          case table.Somea((_, (_, annuler()))) => bdd
          case table.Nonea() =>
            table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
              (table.option[Nat.nat],
                (table.option[Nat.nat],
                  etat))]((c, (m, i)),
              (table.Nonea[Nat.nat](),
                (table.Somea[Nat.nat](n), progress())),
              bdd)
        })
    }

} /* object tp89 */

