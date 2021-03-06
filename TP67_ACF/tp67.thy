theory tp67
imports Main  "~~/src/HOL/Library/Code_Target_Int" 
begin

(* Types des expressions, conditions et programmes (statement) *)
datatype expression= Constant int | Variable string | Sum expression expression | Sub expression expression

datatype condition= Eq expression expression

datatype statement= Seq statement statement | 
                    Aff string expression | 
                    Read string | 
                    Print expression | 
                    Exec expression | 
                    If condition statement statement |
                    Skip
(* Un exemple d'expression *)

(* expr1= (x-10) *)
definition "expr1= (Sub (Variable ''x'') (Constant 10))"


(* Des exemples de programmes *)

(* p1= exec(0) *)
definition "p1= Exec (Constant 0)"
(* p1 est dangereux car il execute l'entier 0, ce qui est décrit comme
dangereux dans l'énoncé*)

(* p2= {
        print(10)
        exec(0+0)
       }
*)
(*p2 dangereux car 0+0 = la tête a toto et aussi 0*)
definition "p2= (Seq (Print (Constant 10)) (Exec (Sum (Constant 0) (Constant 0))))"

(* p3= {
         x:=0
         exec(x)
       }
*)
(*p3 dangereux car on execute x qui est égale à 0*)
definition "p3= (Seq (Aff ''x'' (Constant 0)) (Exec (Variable ''x'')))"

(* p4= {
         read(x)
         print(x+1)
       }
*)
(*p4 pas dangereux car print 0 et non exec 0*)
definition "p4= (Seq (Read ''x'') (Print (Sum (Variable ''x'') (Constant 1))))"


(* Le type des evenements soit X: execute, soit P: print *)
datatype event= X int | P int

(* les flux de sortie, d'entree et les tables de symboles *)

type_synonym outchan= "event list"
definition "el1= [X 1, P 10, X 0, P 20]"                   (* Un exemple de flux de sortie *)

type_synonym inchan= "int list"           
definition "il1= [1,-2,10]"                                (* Un exemple de flux d'entree [1,-2,10]              *)

type_synonym symTable= "(string * int) list"
definition "(st1::symTable)= [(''x'',10),(''y'',12)]"      (* Un exemple de table de symbole *)


(* La fonction (partielle) de recherche dans une liste de couple, par exemple une table de symbole *)
datatype 'a option= None | Some 'a

fun assoc:: "'a \<Rightarrow> ('a * 'b) list \<Rightarrow> 'b option"
where
"assoc _ [] = None" |
"assoc x1 ((x,y)#xs)= (if x=x1 then Some(y) else (assoc x1 xs))"

(* Exemples de recherche dans une table de symboles *)

value "assoc ''x'' st1"     (* quand la variable est dans la table st1 *)
value "assoc ''z'' st1"     (* quand la variable n'est pas dans la table st1 *)


(* Evaluation des expressions par rapport a une table de symboles *)
fun evalE:: "expression \<Rightarrow> symTable \<Rightarrow> int"
where
"evalE (Constant s) e = s" |
"evalE (Variable s) e= (case (assoc s e) of None \<Rightarrow> -1 | Some(y) \<Rightarrow> y)" |
"evalE (Sum e1 e2) e= ((evalE e1 e) + (evalE e2 e))" |
"evalE (Sub e1 e2) e= ((evalE e1 e) - (evalE e2 e))" 

(* Exemple d'évaluation d'expression *)

(* st1 = (x,10)(y,12)*)
(* expr1= (x-10) *)
value "evalE expr1 st1"

(* Evaluation des conditions par rapport a une table de symboles *)
fun evalC:: "condition \<Rightarrow> symTable \<Rightarrow> bool"
where
"evalC (Eq e1 e2) t= ((evalE e1 t) = (evalE e2 t))"

(* Evaluation d'un programme par rapport a une table des symboles, a un flux d'entree et un flux de sortie. 
   Rend un triplet: nouvelle table des symboles, nouveaux flux d'entree et sortie *)
fun evalS:: "statement \<Rightarrow> (symTable * inchan * outchan) \<Rightarrow> (symTable * inchan * outchan)"
where
"evalS Skip x=x" |
"evalS (Aff s e)  (t,inch,outch)=  (((s,(evalE e t))#t),inch,outch)" |
"evalS (If c s1 s2)  (t,inch,outch)=  (if (evalC c t) then (evalS s1 (t,inch,outch)) else (evalS s2 (t,inch,outch)))" |
"evalS (Seq s1 s2) (t,inch,outch)= 
    (let (t2,inch2,outch2)= (evalS s1 (t,inch,outch)) in
        evalS s2 (t2,inch2,outch2))" |
"evalS (Read _) (t,[],outch)= (t,[],outch)" |
"evalS (Read s) (t,(x#xs),outch)= (((s,x)#t),xs,outch)" |
"evalS (Print e) (t,inch,outch)= (t,inch,((P (evalE e t))#outch))" |
"evalS (Exec e) (t,inch,outch)= 
  (let res= evalE e t in
   (t,inch,((X res)#outch)))"




(* Exemples d'évaluation de programmes *)
(* Les programmes p1, p2, p3, p4 ont été définis plus haut *)
(* p1= exec(0) *)

value "evalS p1 ([],[],[])"

(* ------------------------------------ *)
(* p2= {
        print(10)
        exec(0+0)
       }
*)

value "evalS p2 ([],[],[])"

(* ------------------------------------ *)
(* p3= {
         x:=0
         exec(x)
       }
*)

value "evalS p3 ([],[],[])"

(* ------------------------------------ *)
(* p4= {
         read(x)
         print(x+1)
       }
*)

value "evalS p4 ([],[10],[])"


definition "bad1= (Exec (Constant 0))"
definition "bad2= (Exec (Sub (Constant 2) (Constant 2)))"
definition "bad3= (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Variable ''x'')) (Exec (Sub (Variable ''x'') (Constant 1)))))"
definition "bad4= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) Skip (Aff ''y'' (Constant 1))) (Exec (Sum (Variable ''y'') (Constant 1)))))"
definition "bad5= (Seq (Read ''x'') (Seq (Aff ''y'' (Sum (Variable ''x'') (Constant 2))) (Seq (If (Eq (Variable ''x'') (Sub (Constant 0) (Constant 1))) (Seq (Aff ''x'' (Sum (Variable ''x'') (Constant 2))) (Aff ''y'' (Sub (Variable ''y'') (Variable ''x'')))) (Seq (Aff ''x'' (Sub (Variable ''x'') (Constant 2))) (Aff ''y'' (Sub (Variable ''y'') (Variable ''x''))))) (Exec (Variable ''y'')))))"
definition "bad6= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 1)) (Aff ''z'' (Constant 0))) (Exec (Variable ''z''))))"
definition "bad7= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 0)) (Aff ''z'' (Constant 1))) (Exec (Variable ''z''))))"
definition "bad8= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Variable ''x'') (Variable ''y'')) (Exec (Constant 1)) (Exec (Constant 0)))))"
definition "ok0= (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''y'') (Seq (If (Eq (Variable ''y'') (Constant 0)) (Seq (Print (Sum (Variable ''y'') (Variable ''x'')))
(Print (Variable ''x''))
) (Print (Variable ''y''))
) (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Variable ''x''))
 (Seq (Aff ''x'' (Constant 2)) (Seq (Print (Variable ''x''))
 (Seq (Aff ''x'' (Constant 3)) (Seq (Print (Variable ''x''))
 (Seq (Read ''y'') (Seq (If (Eq (Variable ''y'') (Constant 0)) (Aff ''z'' (Sum (Variable ''x'') (Variable ''x''))) (Aff ''z'' (Sub (Variable ''x'') (Variable ''y'')))) (Print (Variable ''z''))
)))))))))))"
definition "ok1= (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Sum (Variable ''x'') (Variable ''x'')))
 (Seq (Exec (Constant 10)) (Seq (Read ''y'') (If (Eq (Variable ''y'') (Constant 0)) (Exec (Constant 1)) (Exec (Constant 2)))))))"
definition "ok2= (Exec (Variable ''y''))"
definition "ok3= (Seq (Read ''x'') (Exec (Sum (Variable ''y'') (Constant 2))))"
definition "ok4= (Seq (Aff ''x'' (Constant 0)) (Seq (Aff ''x'' (Sum (Variable ''x'') (Constant 20))) (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 0)) (Aff ''z'' (Constant 4))) (Seq (Exec (Variable ''z'')) (Exec (Variable ''x''))))))"
definition "ok5= (Seq (Read ''x'') (Seq (Aff ''x'' (Constant 4)) (Exec (Variable ''x''))))"
definition "ok6= (Seq (If (Eq (Constant 1) (Constant 2)) (Aff ''x'' (Constant 0)) (Aff ''x'' (Constant 1))) (Exec (Variable ''x'')))"
definition "ok7= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Constant 1)) (If (Eq (Variable ''x'') (Constant 4)) (Aff ''x'' (Constant 1)) (Aff ''x'' (Constant 1)))) (Exec (Variable ''x''))))"
definition "ok8= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Constant 1)) (Aff ''x'' (Constant 2))) (Exec (Sub (Variable ''x'') (Constant 3)))))"
definition "ok9= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Variable ''x'') (Variable ''y'')) (Constant 0)) (Exec (Constant 1)) (Exec (Sum (Variable ''x'') (Sum (Variable ''y'') (Sum (Variable ''y'') (Variable ''x''))))))))"
definition "ok10= (Seq (Read ''x'') (If (Eq (Variable ''x'') (Constant 0)) (Exec (Constant 1)) (Exec (Variable ''x''))))"
definition "ok11= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Sum (Variable ''x'') (Constant 1))) Skip) (Exec (Variable ''x''))))"
definition "ok12= (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''z'') (If (Eq (Variable ''z'') (Constant 0)) (Exec (Variable ''y'')) (Exec (Variable ''z'')))))"
definition "ok13= (Seq (Aff ''z'' (Constant 4)) (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''y'') (Seq (Aff ''x'' (Sum (Variable ''x'') (Sum (Variable ''z'') (Variable ''x'')))) (Seq (Aff ''z'' (Sum (Variable ''z'') (Variable ''x''))) (Seq (If (Eq (Variable ''y'') (Constant 1)) (Aff ''x'' (Sub (Variable ''x'') (Variable ''y''))) Skip) (Seq (If (Eq (Variable ''y'') (Constant 0)) (Seq (Aff ''y'' (Sum (Variable ''y'') (Constant 1))) (Exec (Variable ''x''))) Skip) (Exec (Variable ''y'')))))))))"
definition "ok14= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Variable ''x'') (Variable ''y'')) (Constant 0)) (Exec (Constant 1)) (Exec (Sum (Variable ''x'') (Variable ''y''))))))"


(* Le TP commence ici! *)
(* TODO: BAD, san0, lemme de correction *)
fun bad:: "(symTable * inchan * outchan) \<Rightarrow> bool"
  where
"bad (t,inch,[]) = False"|
"bad (t,inch,(X a)#xs) = (if(a=0) then True else bad (t,inch,xs))" |
"bad (t,inch,x#xs) = bad (t,inch,xs)"


value "bad ([],[],[])"
value "bad ([], [], [X 0])"
value "bad ([], [], [X 0, P 10])"
value "bad ([(''x'', 0)], [], [X 0])"
value "bad ([(''x'', 0)], [], [P 11])"
(*
Seq statement statement | 
                    Aff string expression | 
                    Read string | 
                    Print expression | 
                    Exec expression | 
                    If condition statement statement |
                    Skip
*)

fun san0 :: "statement \<Rightarrow> bool"
  where
"san0 (Exec x) = False" |
"san0 (Seq s1 s2) = (san0 s1 \<and> san0 s2)" |
"san0 (If c s1 s2) = (san0 s1 \<and> san0 s2)" |
"san0 _ = True"

(*analyse statique lire cm, choisir un domaine abstrait simple et implementer un analyseur statique*)
fun san1 :: "statement \<Rightarrow> bool"
  where
"san1 (Exec (Constant x)) = (x \<noteq> 0)" |
"san1 (Seq x y) = (san1 x \<and> san1 y)" |
"san1 (If c x y) = (san1 x \<and> san1 y)" |
"san1 _ = False"
(*s’il ne comporte que des exec sur des constantes differentes de 0*)
(* donc autre chose = False *)

datatype abs = Undefined | Defined int
type_synonym symTableAbs= "(string * abs) list"

definition "(stAbs::symTableAbs)= [(''x'',Undefined),(''y'',Defined 5),(''z'',Undefined),(''a'',Defined 11)]"


value "assoc ''x'' stAbs"
value "assoc ''y'' stAbs"
value "assoc ''z'' stAbs"
value "assoc ''a'' stAbs"
value "assoc ''n'' stAbs"

fun plusAbs:: "abs \<Rightarrow> abs \<Rightarrow> abs"
  where
"plusAbs Undefined _ = Undefined" |
"plusAbs _ Undefined = Undefined" |
"plusAbs (Defined x) (Defined y) = (if(x+y = 0) then Undefined else Defined (x+y)) "

fun moinAbs:: "abs \<Rightarrow> abs \<Rightarrow> abs"
  where
"moinAbs Undefined _ = Undefined" |
"moinAbs _ Undefined = Undefined" |
"moinAbs (Defined x) (Defined  y) = (if(x-y = 0) then Undefined else Defined (x-y)) "



datatype boolAbs = TrueAbs | FalseAbs | AnyAbs

fun eqAbs :: "abs \<Rightarrow> abs \<Rightarrow> boolAbs"
  where
"eqAbs Undefined _ = AnyAbs"|
"eqAbs _ Undefined = AnyAbs"|
"eqAbs (Defined x) (Defined y) = (if(x=y) then TrueAbs else FalseAbs)"

fun evalE2:: "expression \<Rightarrow> symTableAbs \<Rightarrow> abs"
  where
"evalE2 (Constant c) e = (if(c = 0) then Undefined else Defined c)" |
"evalE2 (Variable s) e= (case (assoc s e) of None \<Rightarrow> Undefined | Some(y) \<Rightarrow> y)" |
"evalE2 (Sum e1 e2) e= (plusAbs (evalE2 e1 e)  (evalE2 e2 e))" |
"evalE2 (Sub e1 e2) e= (moinAbs (evalE2 e1 e)  (evalE2 e2 e))" 

fun evalC2 :: "condition \<Rightarrow> symTableAbs \<Rightarrow> boolAbs"
  where
"evalC2 (Eq e1 e2) t = eqAbs (evalE2 e1 t) (evalE2 e2 t)"

fun combine :: "symTableAbs \<Rightarrow> symTableAbs \<Rightarrow> symTableAbs"
  where
"combine [] t =  t" |
"combine ((x,y)#z) t = 
  (let res = assoc x t in
    (if(res = Some y) then (x,y)#(combine z t)
    else (x,Undefined)#(combine z t)))"


fun evalS2:: "statement \<Rightarrow> (symTableAbs * bool) list \<Rightarrow> (symTableAbs * bool) list"
where
"evalS2 Skip x = x" |
"evalS2 (Aff s e) [] =(let res = evalE2 e [] in
                      (if(res = Undefined) then [([(s,Undefined)],False)] else
                        [([(s,res)],True)]))"|
"evalS2 (Aff s e) ((t,ouch)#rest) = ((((s,(evalE2 e t))#t),ouch)#rest)" |
"evalS2 (If c s1 s2) [] = (let res = evalC2 c [] in
                              (if (res = TrueAbs) then (evalS2 s1 []) else 
                                (if (res = FalseAbs) then (evalS2 s2 [])  else
                                 (let rest1 = (evalS2 s1 []) in
                                   let rest2 = (evalS2 s2 []) in
                                   let (t1,ouch1) =  hd rest1  in
                                   let (t2,ouch2) =  hd rest2  in
                                   let ouch3 = ouch1 \<and> ouch2 in
                                   let rest3 = rest1@rest2 in
                                   let t3 = combine t1 t2 in (t3,ouch3)#rest3))))" |

"evalS2 (If c s1 s2) ((t,ouch)#rest)= 
                             (let res = evalC2 c t in
                              (if (res = TrueAbs) then (evalS2 s1 ((t,ouch)#rest)) else 
                                (if (res = FalseAbs) then (evalS2 s2 ((t,ouch)#rest))  else
                                 (let rest1 = (evalS2 s1 ((t,ouch)#rest)) in
                                   let rest2 = (evalS2 s2 ((t,ouch)#rest)) in
                                   let (t1,ouch1) =  hd rest1  in
                                   let (t2,ouch2) =  hd rest2  in
                                   let ouch3 = ouch1 \<and> ouch2 in
                                   let rest3 = rest1@rest2 in
                                   let t3 = combine t1 t2 in (t3,ouch3)#rest3))))" |

"evalS2 (Seq s1 s2) [] = (let rest1 = (evalS2 s1 []) in
                                   let rest2 = (evalS2 s2 rest1) in
                                   let (t1,ouch1) =  hd rest1  in
                                   let (t2,ouch2) =  hd rest2  in
                                   let ouch3 = ouch1 \<and> ouch2 in
                                   let rest3 = rest1@rest2 in
                                   let t3 = combine t1 t2 in (t3,ouch3)#rest3)"|
"evalS2 (Seq s1 s2) ((t,ouch)#rest)= 
                            (let rest1 = (evalS2 s1 ((t,ouch)#rest)) in
                                   let rest2 = (evalS2 s2 ((t,ouch)#rest1)) in
                                   let (t1,ouch1) =  hd rest1  in
                                   let (t2,ouch2) =  hd rest2  in
                                   let ouch3 = ouch1 \<and> ouch2 in
                                   let rest3 = rest1@rest2 in
                                   let t3 = combine t1 t2 in (t3,ouch3)#rest3)"|
"evalS2 (Read s) [] = [([(s,Defined 1)],True)] "|
"evalS2 (Read s) ((t,ouch)#rest)= (((s,Undefined)#t,ouch)#rest)" |
"evalS2 (Print e) [] = []"|
"evalS2 (Print e) ((t,ouch)#rest)= ((t,ouch)#rest)" |
"evalS2 (Exec e) [] = (let res = evalE2 e [] in 
                       (if(res = Undefined) then [([('''',Undefined)],False)] else  [([('''',res)],True)]))"|
"evalS2 (Exec e) ((t,ouch)#rest)= 
                           (let res= evalE2 e t in
                            (if(res = Undefined \<or> res = Defined 0) then ((t,False)#rest) 
                             else ((t,ouch)#rest)))"
value "evalE2 (Variable y) []"
value "evalS2 (Exec (Variable y)) [] "
fun verifSan:: "(symTableAbs * bool) list \<Rightarrow> bool"
  where
"verifSan [] = True"|
"verifSan ((t,ouch)#xs) = (if(ouch) then verifSan xs else False)"


fun san::"statement \<Rightarrow> bool"
where
"san s = (let res = (evalS2 s (([],True)#Nil)) in (verifSan res))"

value "san bad1"
value "san bad2"
value "san bad3"
value "san bad4"
value "san bad5"
value "san bad6"
value "san bad7"
value "san bad8"

(* Si san accepte un programme alors son évaluation, quelles que soient les entrées utilisateur (inchan)
   ne provoquera pas d'exec(0) *)
(* \<forall>a (san3 P) = True \<rightarrow> \<not>BAD(eval(P,a)) vidéo CM6 timer : 22.22 *)
lemma correction: "(san p \<longrightarrow> \<not>bad(evalS p ([],a,[])))"
  nitpick[timeout=120]
  quickcheck[tester=narrowing,size=5,timeout=120]
  sorry
(* J'ai mis mes autres tentatives pour montrer que j'ai quand même tenter 
d'aller plus loin que 2/6 de score de confiance mais malgrès tout cela, je n'ai pas réussi.

Autres tentatives plus restrictive mais qui laisse passer des exec(0) environ a 190000
datatype abs = Undefined | Defined int | Zero
type_synonym symTableAbs= "(string * abs) list"

definition "(stAbs::symTableAbs)= [(''x'',Undefined),(''y'',Defined 1),(''z'', Defined 9),(''a'',Defined 1)]"

value "assoc ''x'' stAbs"
value "assoc ''y'' stAbs"
value "assoc ''z'' stAbs"
value "assoc ''a'' stAbs"
value "assoc ''n'' stAbs"

fun plusAbs:: "abs \<Rightarrow> abs \<Rightarrow> abs"
  where
"plusAbs Undefined _ = Undefined" |
"plusAbs _ Undefined = Undefined" |
"plusAbs (Defined x) (Defined y) = Defined (x+y)"|
"plusAbs (Defined x) Zero = Defined x "|
"plusAbs Zero (Defined x) = Defined x"|
"plusAbs Zero Zero = Zero "


value "plusAbs Zero Zero"
value "plusAbs Pos Zero"
value "plusAbs Zero Neg"
value "plusAbs Pos Neg"
value "plusAbs Neg Pos"


fun moinAbs:: "abs \<Rightarrow> abs \<Rightarrow> abs"
  where
"moinAbs Undefined _ = Undefined" |
"moinAbs _ Undefined = Undefined" |
"moinAbs (Defined x) (Defined y) = 
  (if(x-y = 0) then Zero else (if(x-y> 0) then Defined (x-y) else Defined (y-x)))"|
"moinAbs (Defined x) Zero = Defined x"|
"moinAbs Zero (Defined x) =  Defined x"|
"moinAbs Zero Zero = Zero "

datatype boolAbs = TrueAbs | FalseAbs | AnyAbs

fun eqAbs :: "abs \<Rightarrow> abs \<Rightarrow> boolAbs"
  where
"eqAbs Undefined _ = AnyAbs"|
"eqAbs _ Undefined = AnyAbs"|
"eqAbs (Defined x) (Defined y) = (if(x=y) then TrueAbs else FalseAbs)"|
"eqAbs (Defined x) Zero = FalseAbs"|
"eqAbs Zero (Defined x) = FalseAbs"|
"eqAbs Zero Zero = TrueAbs "

fun evalE2:: "expression \<Rightarrow> symTableAbs \<Rightarrow> abs"
  where
"evalE2 (Variable s) [] = Undefined "|
"evalE2 (Constant c) e = (if(c = 0) then Zero else Defined c)" |
"evalE2 (Variable s) e= (case (assoc s e) of None \<Rightarrow> Undefined | Some(y) \<Rightarrow> y)" |
"evalE2 (Sum e1 e2) e= (plusAbs (evalE2 e1 e)  (evalE2 e2 e))" |
"evalE2 (Sub e1 e2) e= (moinAbs (evalE2 e1 e)  (evalE2 e2 e))" 


definition "z1= (Constant 1)"
definition "z2= (Constant 3)"
definition "z3= Sub(Variable ''x'') (Variable ''y'')"
definition "z4= Sum(Variable ''x'') (Variable ''y'')"
definition "z5= (Variable ''z'')"
fun evalC2 :: "condition \<Rightarrow> symTableAbs \<Rightarrow> boolAbs"
  where
"evalC2 (Eq e1 e2) t = eqAbs (evalE2 e1 t) (evalE2 e2 t)"

value "evalC2 (Eq z1 z1) []"
value "evalC2 (Eq z1 z3) [(''x'',Pos),(''y'',Pos)]"
value "evalC2 (Eq z3 z3) [(''x'',Pos),(''y'',Pos)]"
value "evalC2 (Eq z5 z4) [(''x'',Pos),(''y'',Pos),(''z'',Pos)]"
value "eqAbs Undefined Undefined"
fun remove ::"(string * abs) \<Rightarrow> symTableAbs \<Rightarrow> symTableAbs"
  where
"remove (x,y) []  = []" |
"remove (x,y) ((a,b)#ts) = (if(a = x \<and> b = y)then ts else (remove (x,y) ts))"

fun combine :: "symTableAbs \<Rightarrow> symTableAbs \<Rightarrow> symTableAbs"
  where
"combine [] t =  t" |
"combine t [] =  t" |
"combine ((x,y)#z) t = 
  (let res = assoc x t in
    (if(res = Some y) then (x,y)#(combine z (remove (x,y) t))
    else (x,Undefined)#(combine z t)))"

value "remove (''a'',Pos) [(''a'',Pos),(''b'',Neg)]"

value "combine[(''s'',Pos)] [(''s'',Pos)]"
fun xor ::"bool\<Rightarrow> bool \<Rightarrow> bool"
  where
"xor True True = True"|
"xor _ _ = False "

fun combine2 :: "(symTableAbs*bool) \<Rightarrow> (symTableAbs*bool) \<Rightarrow> (symTableAbs*bool)"
  where
"combine2 ([],c) (t,c2) = (t,c2)"|
"combine2 (((x,y)#z),c) (t,c2) = 
  (let res = assoc x t in
    (if(res = Some y) then ((x,y)#t,xor c c2)
    else ((x,Undefined)#t,False)))"

fun combine22 :: "(symTableAbs*bool) \<Rightarrow> (symTableAbs*bool) \<Rightarrow> (symTableAbs*bool)"
  where
"combine22 ([],c) (t,c2) = (t,c2)"|
"combine22 (t1,c1) (t2,c2) = 
  ((combine t1 t2),xor c1 c2)"

value "combine2 ([(''s'',Pos)],True) ([(''x'',Zero)],False)"
value "combine2 ([(''s'',Pos)],True) ([(''s'',Zero)],False)"

fun combine3 :: "(symTableAbs*bool)list \<Rightarrow> (symTableAbs*bool)list \<Rightarrow> (symTableAbs*bool)list"
  where
"combine3 [] b = b" |
"combine3 a [] = a "|
"combine3 (x#xs) (y#ys) = (combine22 x y)#(combine3 xs ys)"

value "combine3 [([(''s'',Pos)],True)]  [([(''x'',Neg)],True)] "
value "combine3 [([(''x'',Zero)],False)]  [([(''x'',Neg)],True)] " 

fun evalS2:: "statement \<Rightarrow> (symTableAbs * bool) list \<Rightarrow> (symTableAbs * bool) list"
where
"evalS2 Skip x = x" |

"evalS2 (Aff s e) [] = (let res = evalE2 e [] in
                      (if(res = Undefined) then [([(s,Undefined)],False)] else
                        if(res = Zero) then  [([(s,res)],False)] else  [([(s,res)],True)]))"|

"evalS2 (Aff s e) ((t,ouch)#rest) = ((((s,(evalE2 e t))#t),ouch)#rest)" |

"evalS2 (If c s1 s2) [] = (let res = evalC2 c [] in
                              (if (res = TrueAbs) then (evalS2 s1 []) else 
                                (if (res = FalseAbs) then (evalS2 s2 [])  else
                                 (let rest1 = (evalS2 s1 []) in
                                   (let rest2 = (evalS2 s2 []) in
                                     combine3 rest1 rest2)))))" |

"evalS2 (If c s1 s2) ((t,ouch)#rest)= 
                             (let res = evalC2 c t in
                              (if (res = TrueAbs) then (evalS2 s1 ((t,ouch)#rest)) else 
                                (if (res = FalseAbs) then (evalS2 s2 ((t,ouch)#rest))  else
                                 (let rest1 = (evalS2 s1 ((t,ouch)#rest)) in
                                  (let rest2 = (evalS2 s2  ((t,ouch)#rest1)) in
                                     combine3 rest1 rest2)))))" |

"evalS2 (Seq s1 s2) [] = (let rest1 = (evalS2 s1 []) in
                                 (let rest2 = (evalS2 s2 []) in
                                     combine3 rest1 rest2))" |
"evalS2 (Seq s1 s2) ((t,ouch)#rest)= 
                            (let rest1 = (evalS2 s1 ((t,ouch)#rest)) in
                                   (let rest2 = (evalS2 s2 ((t,ouch)#rest1)) in
                                     combine3 rest1 rest2))" |
"evalS2 (Read s) [] = [([(''s'',Undefined)],False)] "|
"evalS2 (Read s) ((t,ouch)#rest)= (((s,Undefined)#t,ouch)#rest)" |

"evalS2 (Print e) [] = []"|
"evalS2 (Print e) ((t,ouch)#rest)= ((t,ouch)#rest)" |

"evalS2 (Exec e) [] = (let res = evalE2 e [] in
                      (if(res = Undefined \<or> res = Zero) then [([([],Undefined)],False)] else [([(''n'',res)],True)]))"|
"evalS2 (Exec e) ((t,ouch)#rest)= 
                           (let res= evalE2 e t in
                            (if(res = Undefined \<or> res = Zero) then ((t,False)#rest) 
                             else ((t,ouch)#rest)))"
(*(Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Variable ''x'') (Variable ''y'')) (Exec (Constant 1)) (Exec (Constant 0)))))"*)
value "evalE2 (Variable y) []"
value "evalS2 (Exec (Variable ''y'')) [] "
value "evalS2 (Exec (Variable ''y'')) [([(''y'',Zero)],True)] "
value "evalS2 bad1 []"
value "evalS2 bad2 []"
value "evalS2 bad3 []"
value "evalS2 bad4 []"
value "evalS2 bad5 []"
value "evalS2 bad6 []"
value "evalS2 bad7 []"
value "evalS2 bad8 []"
value "evalS2 (Seq (Read ''x'') (Seq(Read ''y'') (Exec(Variable ''x'')))) []"

fun verifSan:: "(symTableAbs * bool) list \<Rightarrow> bool"
  where
"verifSan [] = True"|
"verifSan ((t,ouch)#xs) = (if(ouch) then verifSan xs else False)"

value "verifSan (evalS2 bad1 [])"
value "verifSan (evalS2 bad2 [])"
value "verifSan (evalS2 bad3 [])"
value "verifSan (evalS2 bad4 [])"
value "verifSan (evalS2 bad5 [])"
value "verifSan (evalS2 bad6 [])"
value "verifSan (evalS2 bad7 [])"
value "verifSan (evalS2 bad8 [])"

fun san::"statement \<Rightarrow> bool"
where
"san s = (let res = (evalS2 s []) in (verifSan res))"


value "san bad1"
value "san bad2"
value "san bad3"
value "san bad4"
value "san bad5"
value "san bad6"
value "san bad7"
value "san bad8"

value "san ok1"
value "san ok2"
value "san ok3"
value "san ok4"
value "san ok5"
value "san ok6"
value "san ok7"
value "san ok8"
-------------------------------------+
datatype abs = Undefined | Defined int
type_synonym symTableAbs= "(string * abs) list"

definition "(stAbs::symTableAbs)= [(''x'',Undefined),(''y'',Defined 5),(''z'',Undefined),(''a'',Defined 11)]"


value "assoc ''x'' stAbs"
value "assoc ''y'' stAbs"
value "assoc ''z'' stAbs"
value "assoc ''a'' stAbs"
value "assoc ''n'' stAbs"

fun plusAbs:: "abs \<Rightarrow> abs \<Rightarrow> abs"
  where
"plusAbs Undefined _ = Undefined" |
"plusAbs _ Undefined = Undefined" |
"plusAbs (Defined x) (Defined y) = (if(x+y = 0) then Undefined else Defined (x+y)) "

fun moinAbs:: "abs \<Rightarrow> abs \<Rightarrow> abs"
  where
"moinAbs Undefined _ = Undefined" |
"moinAbs _ Undefined = Undefined" |
"moinAbs (Defined x) (Defined  y) = (if(x-y = 0) then Undefined else Defined (x-y)) "



datatype boolAbs = TrueAbs | FalseAbs | AnyAbs

fun eqAbs :: "abs \<Rightarrow> abs \<Rightarrow> boolAbs"
  where
"eqAbs Undefined _ = AnyAbs"|
"eqAbs _ Undefined = AnyAbs"|
"eqAbs (Defined x) (Defined y) = (if(x=y) then TrueAbs else FalseAbs)"

fun evalE2:: "expression \<Rightarrow> symTableAbs \<Rightarrow> abs"
  where
"evalE2 (Constant c) e = (if(c = 0) then Undefined else Defined c)" |
"evalE2 (Variable s) e= (case (assoc s e) of None \<Rightarrow> Undefined | Some(y) \<Rightarrow> y)" |
"evalE2 (Sum e1 e2) e= (plusAbs (evalE2 e1 e)  (evalE2 e2 e))" |
"evalE2 (Sub e1 e2) e= (moinAbs (evalE2 e1 e)  (evalE2 e2 e))" 

fun evalC2 :: "condition \<Rightarrow> symTableAbs \<Rightarrow> boolAbs"
  where
"evalC2 (Eq e1 e2) t = eqAbs (evalE2 e1 t) (evalE2 e2 t)"
fun remove ::"(string * abs) \<Rightarrow> symTableAbs \<Rightarrow> symTableAbs"
  where
"remove (x,y) []  = []" |
"remove (x,y) ((a,b)#ts) = (if(a = x \<and> b = y)then ts else (remove (x,y) ts))"

fun combine :: "symTableAbs \<Rightarrow> symTableAbs \<Rightarrow> symTableAbs"
  where
"combine [] t =  t" |
"combine t [] =  t" |
"combine ((x,y)#z) t = 
  (let res = assoc x t in
    (if(res = Some y) then (x,y)#(combine z (remove (x,y) t))
    else (x,Undefined)#(combine z t)))"

value "remove (''a'',Pos) [(''a'',Pos),(''b'',Neg)]"

value "combine[(''s'',Pos)] [(''s'',Pos)]"
fun xor ::"bool\<Rightarrow> bool \<Rightarrow> bool"
  where
"xor True True = True"|
"xor _ _ = False "

fun combine22 :: "(symTableAbs*bool) \<Rightarrow> (symTableAbs*bool) \<Rightarrow> (symTableAbs*bool)"
  where
"combine22 ([],c) (t,c2) = (t,c2)"|
"combine22 (t1,c1) (t2,c2) = 
  ((combine t1 t2),xor c1 c2)"

value "combine22 ([(''s'',Pos)],True) ([(''x'',Zero)],False)"
value "combine22 ([(''s'',Pos)],True) ([(''s'',Zero)],False)"

fun combine3 :: "(symTableAbs*bool)list \<Rightarrow> (symTableAbs*bool)list \<Rightarrow> (symTableAbs*bool)list"
  where
"combine3 [] b = b" |
"combine3 a [] = a "|
"combine3 (x#xs) (y#ys) = (combine22 x y)#(combine3 xs ys)"


fun evalS2:: "statement \<Rightarrow> (symTableAbs * bool) list \<Rightarrow> (symTableAbs * bool) list"
where
"evalS2 Skip x = x" |
"evalS2 (Aff s e) [] =(let res = evalE2 e [] in
                      (if(res = Undefined) then [([(s,Undefined)],False)] else
                        [([(s,res)],True)]))"|
"evalS2 (Aff s e) ((t,ouch)#rest) = ((((s,(evalE2 e t))#t),ouch)#rest)" |
"evalS2 (If c s1 s2) [] = (let res = evalC2 c [] in
                              (if (res = TrueAbs) then (evalS2 s1 []) else 
                                (if (res = FalseAbs) then (evalS2 s2 [])  else
                                 (let rest1 = (evalS2 s1 []) in
                                    let rest2 = (evalS2 s2 []) in
                                       combine3 rest1 rest2))))" |

"evalS2 (If c s1 s2) ((t,ouch)#rest)= 
                             (let res = evalC2 c t in
                              (if (res = TrueAbs) then (evalS2 s1 ((t,ouch)#rest)) else 
                                (if (res = FalseAbs) then (evalS2 s2 ((t,ouch)#rest))  else
                                 (let rest1 = (evalS2 s1 ((t,ouch)#rest)) in
                                   let rest2 = (evalS2 s2 ((t,ouch)#rest)) in
                                    combine3 rest1 rest2))))
                                   " |

"evalS2 (Seq s1 s2) [] = (let rest1 = (evalS2 s1 []) in
                            let rest2 =( evalS2 s2 []) in
                                combine3 rest1 rest2)
                                   "|
"evalS2 (Seq s1 s2) ((t,ouch)#rest)= 
                            (let rest1 = (evalS2 s1 ((t,ouch)#rest)) in
                               let rest2 = (evalS2 s2 ((t,ouch)#rest)) in
                                combine3 rest1 rest2)
                                   "|
"evalS2 (Read s) [] = [([(s,Defined 1)],True)] "|
"evalS2 (Read s) ((t,ouch)#rest)= (((s,Undefined)#t,ouch)#rest)" |
"evalS2 (Print e) [] = []"|
"evalS2 (Print e) ((t,ouch)#rest)= ((t,ouch)#rest)" |
"evalS2 (Exec e) [] = (let res = evalE2 e [] in 
                       (if(res = Undefined) then [([('''',Undefined)],False)] else  [([('''',res)],True)]))"|
"evalS2 (Exec e) ((t,ouch)#rest)= 
                           (let res= evalE2 e t in
                            (if(res = Undefined \<or> res = Defined 0) then ((t,False)#rest) 
                             else ((t,ouch)#rest)))"

value "evalE2 (Variable y) []"
value "evalS2 (Exec (Variable y)) [] "
fun verifSan:: "(symTableAbs * bool) list \<Rightarrow> bool"
  where
"verifSan [] = True"|
"verifSan ((t,ouch)#xs) = (if(ouch) then verifSan xs else False)"


fun san::"statement \<Rightarrow> bool"
where
"san s = (let res = (evalS2 s (([],True)#Nil)) in (verifSan res))"

value "san bad1"
value "san bad2"
value "san bad3"
value "san bad4"
value "san bad5"
value "san bad6"
value "san bad7"
value "san bad8"
*)

(* ----- Restriction de l'export Scala (Isabelle 2018) -------*)
(* ! ! !  NE PAS MODIFIER ! ! ! *)
(* Suppression de l'export des abstract datatypes (Isabelle 2018) *)
code_reserved Scala
  expression condition statement 
code_printing
   type_constructor expression \<rightharpoonup> (Scala) "expression"
  | constant Constant \<rightharpoonup> (Scala) "Constant"
  | constant Variable \<rightharpoonup> (Scala) "Variable"
  | constant Sum \<rightharpoonup> (Scala) "Sum"
  | constant Sub \<rightharpoonup> (Scala) "Sub"  

  | type_constructor condition \<rightharpoonup> (Scala) "condition"
  | constant Eq \<rightharpoonup> (Scala) "Eq"

  | type_constructor statement \<rightharpoonup> (Scala) "statement"
  | constant Seq \<rightharpoonup> (Scala) "Seq"
  | constant Aff \<rightharpoonup> (Scala) "Aff"
  | constant Read \<rightharpoonup> (Scala) "Read"
  | constant Print \<rightharpoonup> (Scala) "Print"
  | constant Exec \<rightharpoonup> (Scala) "Exec"
  | constant If \<rightharpoonup> (Scala) "If"
  | constant Skip \<rightharpoonup> (Scala) "Skip"
  | code_module "" \<rightharpoonup> (Scala) 
{* // Code generated by Isabelle
package tp67

import utilities.Datatype._
// automatic conversion of utilities.Datatype.Int.int to Int.int
object AutomaticConversion{ 
	implicit def int2int(i:utilities.Datatype.Int.int):Int.int =
			i match {
			case utilities.Datatype.Int.int_of_integer(i)=>Int.int_of_integer(i)
	}
	
	def bit_cut_integer(k: BigInt): (BigInt, Boolean) =
  (if (k == BigInt(0)) (BigInt(0), false)
    else {
           val (r, s): (BigInt, BigInt) =
             ((k: BigInt) => (l: BigInt) => if (l == 0) (BigInt(0), k) else
               (k.abs /% l.abs)).apply(k).apply(BigInt(2));
           ((if (BigInt(0) < k) r else (- r) - s), s == BigInt(1))
         })
         
	def char_of_integer(k: BigInt): String.char =
  {
    val (q0, b0): (BigInt, Boolean) = bit_cut_integer(k)
    val (q1, b1): (BigInt, Boolean) = bit_cut_integer(q0)
    val (q2, b2): (BigInt, Boolean) = bit_cut_integer(q1)
    val (q3, b3): (BigInt, Boolean) = bit_cut_integer(q2)
    val (q4, b4): (BigInt, Boolean) = bit_cut_integer(q3)
    val (q5, b5): (BigInt, Boolean) = bit_cut_integer(q4)
    val (q6, b6): (BigInt, Boolean) = bit_cut_integer(q5)
    val a: (BigInt, Boolean) = bit_cut_integer(q6)
    val (_, aa): (BigInt, Boolean) = a;
    String.Chara(b0, b1, b2, b3, b4, b5, b6, aa)
  }
	
  def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
    case (f, Nil) => Nil
    case (f, x :: xs) => f(x) :: map[A, B](f, xs)
  }

	def explodeList(l: List[Char]): List[String.char] ={
       (l.map(c => { val k: Int = c.toInt; if (k < 128) BigInt(k) else sys.error("Non-ASCII character in literal") })).map(a => char_of_integer(a))
    }
	
	def explode(s: String): List[String.char] ={
	    explodeList(s.toCharArray.toList)
	}
	
	// conversion from Scala String to HOL string
  implicit def string2charList(s:String):List[String.char]= explode(s)
  
  // conversion from Scala List[Char] to HOL List[String.char]
  implicit def charList2charList(l:List[Char]):List[String.char]= explodeList(l)
  // conversion of a pair with a Scala List[String] on the first position
  // to an HOL pair with an HOL List[String.char] on first position
	implicit def tupleString2tupleString[T](t:(List[Char],T)):
	    (List[String.char],T)= t match { case (e1,e2) => (charList2charList(e1),e2)}

  // conversion from Isabelle Int.int to Project Int.int
  implicit def int2Dataint(i:Int.int):utilities.Datatype.Int.int =
            i match {
            case Int.int_of_integer(i)=>utilities.Datatype.Int.int_of_integer(i)
    }

   def stringChar2char(x: String.char): Char = {
        x match {
          case String.Chara(x1,x2,x3,x4,x5,x6,x7,x8) => {
            var n = 0;
            n = if (x8) 2*n+1 else 2*n;
            n = if (x7) 2*n+1 else 2*n;
            n = if (x6) 2*n+1 else 2*n;
            n = if (x5) 2*n+1 else 2*n;
            n = if (x4) 2*n+1 else 2*n;
            n = if (x3) 2*n+1 else 2*n;
            n = if (x2) 2*n+1 else 2*n;
            n = if (x1) 2*n+1 else 2*n;
            n.toChar
          }
        }
      }

    // conversion from Isabelle String to Lists of Chars
    implicit def charList2String(l: List[String.char]): List[Char] = {
          l.map(stringChar2char(_))
    } 
}

import AutomaticConversion._
*}


(* Directive pour l'exportation de l'analyseur *)

export_code san in Scala (case_insensitive)

(* file "~/workspace/TP67/src/tp67/san.scala"   (* à adapter en fonction du chemin de votre projet TP67 *)
*)

end
