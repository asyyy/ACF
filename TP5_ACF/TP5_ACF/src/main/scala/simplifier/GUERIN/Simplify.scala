package simplifier.GUERIN
import library._

class MySimplifier extends Simplifier{
	/**
	 * Permet de simplifier les glob
	 * @param p représente la chaîne de caractère que l'on veut simplifier par une liste de symbole
	 * @return une liste de symbole simplifié si possible
	 */
	def simplify(p: List[Symbol]): List[Symbol] = {
		p match {
			case Nil => Nil
			case rest :: Nil => List(rest)

			case Char(a) :: m => Char(a) :: simplify(m)
			case x :: Char(a) :: m => x ::Char(a) :: simplify(m)

			case Star:: Star:: m => Star :: simplify(m)
			case Star:: Qmark:: m => Plus :: simplify(m)
			case Star:: Plus:: m => Plus :: simplify(m)

			case Qmark:: Star:: m => Plus :: simplify(m)
			case Qmark:: Qmark:: m => Qmark :: Qmark :: simplify(m)
			case Qmark:: Plus:: m => Qmark :: Plus :: simplify(m)

			case Plus:: Star:: m => Plus :: simplify(m)
			case Plus:: Qmark:: m => Plus :: Qmark :: simplify(m)
			case Plus:: Plus:: m => Plus :: Plus :: simplify(m)
		}
	}
}