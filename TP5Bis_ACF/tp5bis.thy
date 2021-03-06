theory tp5bis
  imports Main 
begin

(* les glob sont les chaînes unix qui utilisent les jokers ?, * et + pour décrire des ensembles de noms *)

(* Définition du type glob (ici nommé pattern) *)
datatype symbol = Char char | Star | Qmark | Plus

type_synonym word= "char list"
type_synonym pattern= "symbol list" 

(* La fonction qui dit si un mot est accepté par un pattern/glob  *)
fun accept::"pattern \<Rightarrow> word \<Rightarrow> bool"
  where
"accept [] [] = True" |
"accept [Star] _ = True" |
"accept [] (_#_) = False" |
"accept ((Char x)#_) [] = False" | 
"accept ((Char x)#r1) (y#r2) = (if x=y then (accept r1 r2) else False)"  |
"accept (Qmark#r1) [] = False" |
"accept (Qmark#r1) (_#r2) = (accept r1 r2)" |
"accept (Plus#r1) [] = False" |
"accept (Plus#r1) (a#r2) = (accept (Star#r1) r2)" |
"accept (Star#r1) [] = (accept r1 [])" |
"accept (Star#r1) (a#r2) = ((accept r1 (a#r2)) \<or> (accept r1 r2) \<or> (accept (Star#r1) r2))"

(* Les caractères en Isabelle/HOL *)
value "(CHR ''a'')"

(* Quelques exemples d'utilisation de la fonction accept *)
value "accept [Star,(Char (CHR ''a''))] [(CHR ''a'')]"
value "accept [Star,(Char (CHR ''a''))] [(CHR ''b''),(CHR ''a'')]"
value "accept [Star,(Char (CHR ''a''))] [(CHR ''a''),(CHR ''b'')]"
value "accept [Star,Star] []"
value "accept [Plus,Star,Star] []"

(* ----------------------------- Votre TP commence ici! ---------------------------------------- *)
(*pattern = symbol list*)
fun simplify::"pattern \<Rightarrow> pattern"
  where

"simplify [] = []" |
"simplify [Star] = [Star]" |
"simplify [Qmark] = [Qmark]" |
"simplify [Plus] = [Plus]" |

"simplify [Char a ] = [Char a]"|
"simplify ((Char a ) # m) = (Char a)#simplify(m)"|


"simplify (Star#(Char a)#m) = (Star#(Char a)#simplify(m))" |
"simplify (Qmark#(Char a)#m) = (Qmark#(Char a)#simplify(m))" |
"simplify (Plus#(Char a)#m) = (Plus#(Char a)#simplify(m))" |

"simplify (Star#Star#m) = Star#simplify(m)" |
"simplify (Star#Qmark#m) = Plus#simplify(m)" |
"simplify (Star#Plus#m) = Plus#simplify(m)" |

"simplify (Qmark#Star#m) = Plus#simplify(m)" |
"simplify (Qmark#Qmark#m) = Qmark#Qmark#simplify(m)" |
"simplify (Qmark#Plus#m) = Qmark#Plus#simplify(m)" |

"simplify (Plus#Star#m) = Plus#simplify(m)" |
"simplify (Plus#Qmark#m) = Plus#Qmark#simplify(m)" |
"simplify (Plus#Plus#m) = Plus#Plus#simplify(m)"

value "simplify [Star,Qmark]"
value "accept [Star,Star] []"
value "accept [Star] []"

(*nitpick[timeout=120]*)
(*apply (induct p arbitraty:w rule:simplify.induct) *)

(* Le lemme de correction de la fonction simplify... Pour le prouver voir les lemmes intermédiaires à définir, plus bas. *)
lemma correction : "accept p w \<longleftrightarrow> accept (simplify p) w"
  nitpick[timeout=120]
  quickcheck [tester=narrowing]
  oops


(* Le lemme de minimalité dit que le pattern simplifié est le plus petit de tous les
   patterns équivalents. Reformulé ici sous la forme de sa contraposée: s'il existe un pattern 
   plus petit que le pattern simplifié alors il n'est pas équivalent. Il n'est pas équivalent
   si il existe au moins pour lequel l'acceptation par "accept" sera différente. *)

lemma mini :"((length p)< (length (simplify p2))) \<longrightarrow> (\<exists> w. (accept p w) \<noteq> (accept (simplify p2) w))"
 (* La preuve de ce lemme n'est pas demandée. *)
 (* Utiliser le lemme suivant pour trouver des contre-exemples *)
  oops

(* Pour trouver (efficacement) des contre-exemples sur ce lemme de minimalité, on va limiter 
   la complexité des patterns considérés qu'on nommera "basicPattern" : Ici des patterns 
    avec *, ?, + et uniquement le caractère A *)


fun basicPattern:: "pattern \<Rightarrow> bool"
  where
"basicPattern [] = True" |
"basicPattern ((Char CHR ''A'') # r) = basicPattern r" |
"basicPattern ((Char _) # r) = False" |
"basicPattern (_ # r) = basicPattern r"

(* Le lemme de minimalité pour les basicPatterns *)
lemma mini2: "(basicPattern p) \<longrightarrow> ((length p)< (length (simplify p2))) \<longrightarrow> (\<exists> w. (accept p w) \<noteq> (accept (simplify p2) w))"
  quickcheck [tester=narrowing,timeout=00]
   (* nitpick ne trouve que des contre-exemples qui n'en sont pas *)
  oops

(* La directive d'export du code Scala *)
(* A ne pas modifier! *)
code_reserved Scala
  symbol 
code_printing
   type_constructor symbol \<rightharpoonup> (Scala) "Symbol"
   | constant Char \<rightharpoonup> (Scala) "Char"
   | constant Star \<rightharpoonup> (Scala) "Star"
   | constant Plus \<rightharpoonup> (Scala) "Plus"
   | constant Qmark \<rightharpoonup> (Scala) "Qmark"

export_code simplify in Scala


(* Pour prouver le lemme de correction, il vous sera nécessaire de prouver tous ces lemmes intermédiaires! *)

(* Le pattern vide n'accepte que le mot vide *)
lemma acceptVide: "(accept [] w) \<longrightarrow> w=[]"
  apply (induct w)
  apply auto
  done
  
(* Le seul pattern n'acceptant que le mot vide est le pattern vide *)
lemma acceptVide2: "(\<forall> w. w\<noteq>[] \<longrightarrow> \<not>(accept p w)) \<longrightarrow> p=[]"
  apply (induct p )
  apply simp
proof -
fix a :: symbol and pa :: "symbol list"
assume a1: "(\<forall>w. w \<noteq> [] \<longrightarrow> \<not> accept pa w) \<longrightarrow> pa = []"
  obtain cc :: "symbol \<Rightarrow> char" where
      f2: "\<forall>s cs ss. (((s = Star \<or> s = Qmark) \<or> s = Plus) \<or> accept (s # ss) (cc s # cs)) \<or> \<not> accept ss cs"
    by (metis (no_types) accept.simps(5) symbol.exhaust)
  have "pa = [] \<longrightarrow> (\<exists>cs. ((a \<noteq> Plus \<and> a \<noteq> Qmark) \<and> a \<noteq> Star) \<and> accept pa cs) \<or> (\<exists>cs. cs \<noteq> [] \<and> accept [a] cs)"
    by (metis accept.simps(1) accept.simps(2) accept.simps(7) accept.simps(9) neq_Nil_conv)
  moreover
{ assume "pa \<noteq> []"
then have "((\<forall>cs. cs \<noteq> [] \<longrightarrow> \<not> accept (a # pa) cs) \<longrightarrow> a # pa = []) \<or> (\<exists>cs. ((a \<noteq> Plus \<and> a \<noteq> Qmark) \<and> a \<noteq> Star) \<and> accept pa cs)"
using a1 by (metis accept.simps(11) accept.simps(7) accept.simps(9) neq_Nil_conv) }
  ultimately show "(\<forall>cs. cs \<noteq> [] \<longrightarrow> \<not> accept (a # pa) cs) \<longrightarrow> a # pa = []"
    using f2 by blast
qed

  
  
(* Le seul pattern n'acceptant que le langage ? est ? *)
lemma acceptQmark: "(\<forall> w. (accept [Qmark] w = (accept p w))) \<longrightarrow> p=[Qmark]"
  apply (induct p)
  using acceptVide acceptVide2 apply blast
   by (metis accept.simps(11) accept.simps(2) accept.simps(5) accept.simps(7) accept.simps(9) acceptVide acceptVide2 basicPattern.simps(1) basicPattern.simps(10) basicPattern.simps(2) list.exhaust symbol.exhaust)
 
  

(* Si le pattern commence par un caractère ou un point d'interrogation alors le mot accepté
   commence forcément par un caractère (il ne peut être vide) *)
lemma charAndQmarkRemoval: "((x\<noteq>Star) \<and> (x\<noteq> Plus) \<and> (accept (x#r) m)) \<longrightarrow> (\<exists> x2 r2. m=x2#r2 \<and> (accept r r2))"
  apply (induct m)
   apply (simp add:acceptQmark)
  apply (metis accept.simps(4) accept.simps(6) symbol.exhaust)
  apply simp
  by (metis accept.simps(5) accept.simps(7) symbol.exhaust)

(* Si le pattern commence par une étoile, on peut soit l'oublier soit oublier le premier caractère du mot accepté *)
lemma patternStartsWithStar: "((accept (Star#r) m)) \<longrightarrow> ((accept r m) \<or> (\<exists> x2 r2. m=x2#r2 \<and> (accept (Star#r) r2)))"

 apply (induct m)
   apply simp
   apply (metis accept.simps(1) accept.simps(10) list.exhaust)
  by (metis accept.simps(10) accept.simps(11) accept.simps(2) splice.elims)
    
(* On peut compléter à gauche n'importe quel pattern par une étoile *)
lemma completePatternWithStar: "(accept r m) \<longrightarrow> (accept (Star#r) m)"
  apply (induct m)
   apply (metis accept.simps(10) accept.simps(2) list.exhaust)
  by (metis accept.simps(11) accept.simps(3) neq_Nil_conv)
    
lemma completePatternWithStar2: "(accept r m) \<longrightarrow> (accept (Star#r) (m1@m))"
  apply (induct m1)
   apply (simp add: completePatternWithStar)
  by (smt Cons_eq_appendI accept.simps(11) accept.simps(2) acceptVide append.right_neutral list.discI list.inject list.sel(3) remdups_adj.elims remdups_adj_Cons_alt)
   
  

 (*On peut oublier une étoile dès qu'il y en a une juste après *)
lemma forgetOneStar:"(accept (Star#(Star#r)) w) = (accept (Star#r) w)"
  apply (induct w)
   apply simp
  by (smt accept.simps(11) accept.simps(2) remdups_adj.elims)

(* Etoile suivie de point d'interrogation est équivalent à point d'interrogation étoile *)
lemma starQmark:"((accept (Star#(Qmark#r)) w) = (accept (Qmark#(Star#r)) w))"
  apply (induct w)
   apply simp
  using charAndQmarkRemoval completePatternWithStar forgetOneStar patternStartsWithStar by fastforce

  
(* Si deux patterns sont équivalents on peut les compléter à gauche... *)

(* ... par une étoile *)
lemma equivalentPatternStar:"((\<forall> w1. (accept p1 w1) = (accept p2 w1))) \<longrightarrow> ((accept (Star#p1) w) = (accept (Star#p2) w))"
  apply (induct w)
  using completePatternWithStar patternStartsWithStar apply blast
  by (smt accept.simps(11) completePatternWithStar forgetOneStar list.sel(3) patternStartsWithStar)
    
(* ... par un caractère (identique) *)
lemma equivalentPatternChar:"((\<forall> w. (accept p1 w) = (accept p2 w))) \<longrightarrow> ((accept ((Char x)#p1) w) = (accept ((Char x)#p2) w))"
 by (metis (full_types) accept.simps(5) charAndQmarkRemoval symbol.distinct(1) symbol.distinct(5))
  
(* ... par un point d'interrogation *)
lemma equivalentPatternQmark:"((\<forall> w. (accept p1 w) = (accept p2 w))) \<longrightarrow> ((accept (Qmark#p1) w) = (accept (Qmark#p2) w))"
  apply (induct w)
   apply simp
  apply auto
  done

(* Par un plus *)
lemma equivalentPatternPlus:"((\<forall> w. (accept p1 w) = (accept p2 w))) \<longrightarrow> ((accept (Plus#p1) w) = (accept (Plus#p2) w))"
  apply (induct w)
   apply simp
  by (simp add: equivalentPatternStar)
  

lemma plusStarQmark:"((accept (Star#(Qmark#r)) w) = (accept (Plus#r) w))"
  apply (induct w)
   apply simp
  using accept.simps(7) accept.simps(9) starQmark by blast
  

lemma plusStarStar:"((accept (Plus#(Star#r)) w) = (accept (Plus#r) w))"
  apply (induct w)
   apply simp
  by (simp add: forgetOneStar)
  

lemma plusPlus1:"((accept (Plus#(Plus#r)) w) = (accept (Qmark#(Plus#r)) w))"
  apply (induct w)
   apply simp
  by (metis accept.simps(11) accept.simps(7) accept.simps(9) patternStartsWithStar plusStarQmark)
  
(* Le lemme de correction final *)
lemma correction:"accepte p w \<longleftrightarrow> accepte (simplify p) w"
  apply (induct p rule : simplify.induct)
  by(simp_all)
  
  
  



  
end
 