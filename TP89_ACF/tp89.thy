theory tp89
 
  imports Main table "~~/src/HOL/Library/Code_Target_Nat" (* pour l'export Scala *)

begin

(* 
quickcheck_params [size=6,tester=narrowing,timeout=120]
nitpick_params [timeout=120]
*)

type_synonym transid= "nat*nat*nat"

datatype message= 
  Pay transid nat  
| Ack transid nat
| Cancel transid

datatype etat = valide | progress | annuler

type_synonym transaction= "transid * nat"
(* Table id \<Rightarrow> transid | value \<Rightarrow> Prix Max, Prix Min, Etat de la transaction*)

type_synonym transBdd = "(transid ,(nat option * nat option * etat)) table"

fun removeDoublonAux :: "message \<Rightarrow> message list \<Rightarrow> message list"
  where
"removeDoublonAux x [] = [x]"|
"removeDoublonAux x (y#li) = (if(x=y)then [] else removeDoublonAux x li) "

fun removeDoublon :: "message list \<Rightarrow> message list"
  where
"removeDoublon [] = []" |
"removeDoublon (x#xs) = append (removeDoublonAux x xs)  (removeDoublon xs)"

value "removeDoublon [(Cancel (1,2,3)),(Cancel (1,2,3))]"
value "removeDoublon [(Cancel (1,2,3)),(Cancel (1,2,4))]"
value "removeDoublon [(Pay (1,2,3) 6),(Cancel (1,2,3))]"
value "removeDoublon [(Pay (1,2,3) 6),(Pay (1,2,3) 6)]"
value "removeDoublon [(Cancel (1,2,3))]"


fun rmDoublonTransAux ::"transaction \<Rightarrow> transaction list \<Rightarrow> transaction list"
  where
"rmDoublonTransAux x [] = [x]" |
"rmDoublonTransAux x (y#li) = (if(x = y) then [] else rmDoublonTransAux x li)"

fun rmDoublonTrans ::"transaction list \<Rightarrow> transaction list"
  where
"rmDoublonTrans [] = []" |
"rmDoublonTrans (x#xs) = append (rmDoublonTransAux x xs) (rmDoublonTrans xs)" 

value "rmDoublonTrans []"
value "rmDoublonTrans [((1,2,3),1)]"
value "rmDoublonTrans [((1,2,3),1),((1,2,3),1)]"
value "rmDoublonTrans [((1,2,3),1),((1,2,3),2)]"

fun egOptOpt :: "nat option \<Rightarrow> nat option \<Rightarrow> bool"
  where
"egOptOpt (Some x) (Some y) = (if(x = y) then True else False)" |
"egOptOpt _ _ = False"

fun egOptNat :: "nat option \<Rightarrow> nat  \<Rightarrow> bool"
  where
"egOptNat (Some x)  y = (if(x = y) then True else False)" |
"egOptNat _ _ = False"

fun supOptNat :: "nat option \<Rightarrow> nat  \<Rightarrow> bool"
  where
"supOptNat (Some x)  y = (if(x < y) then True else False)" |
"supOptNat _ _ = False"

fun infOptNat :: "nat option \<Rightarrow> nat  \<Rightarrow> bool"
  where
"infOptNat (Some x)  y = (if(x > y) then True else False)" |
"infOptNat _ _ = False"

fun traiterMessage :: "message \<Rightarrow> transBdd \<Rightarrow> transBdd"
  where
"traiterMessage (Cancel i) bdd = 
  (case assoc i bdd of 
  None \<Rightarrow>  bdd |
  Some(res) \<Rightarrow> let(a,b,c) = res in modify i (a,b,annuler) bdd)" |

(* Si n'existe pas : on l'ajoute avec l'état progress
   si trouve et etat = progress :  on regarde selon valeur précédente et adapte
   si trouve et etat != progress : on touche a rien*)

"traiterMessage (Pay (c,m,i) n) bdd = 
  (case assoc (c,m,i) bdd of 
  None \<Rightarrow> modify (c,m,i) (Some n,None,progress) bdd |
  Some (client,marchant,progress) \<Rightarrow> 
  (if(supOptNat marchant n \<and> n \<noteq> 0 \<and> marchant \<noteq> Some 0) then modify (c,m,i) (Some n, Some n,valide) bdd else 
   (if(egOptNat marchant n \<and> n \<noteq> 0 \<and> marchant \<noteq> Some 0) then modify (c,m,i) (Some n,marchant,valide) bdd else 
    (if((supOptNat client n) \<or> client = None ) then modify (c,m,i) (Some n,marchant,progress) bdd else bdd)))|
  Some(client,marchant,_) \<Rightarrow> bdd)"|

"traiterMessage (Ack (c,m,i) n) bdd = 
  (case assoc (c,m,i) bdd of 
  None \<Rightarrow> modify (c,m,i) (None,Some n,progress) bdd |
  Some (client,marchant,progress) \<Rightarrow> 
  (if(infOptNat client n \<and> n \<noteq> 0 \<and> client \<noteq> Some 0) then modify (c,m,i) (client, client,valide) bdd else 
   (if(egOptNat client n \<and> n \<noteq> 0 \<and> client \<noteq> Some 0) then modify (c,m,i) (client, Some n,valide) bdd else 
    (if((infOptNat marchant n) \<or> marchant = None ) then modify (c,m,i) (client, Some n,progress) bdd else bdd)))|
  Some(client,marchant,_) \<Rightarrow> bdd)"


fun getVal::"nat option \<Rightarrow> nat"
  where
"getVal (Some x) = x"|
"getVal None = 0"

fun pasDansBdd :: "nat \<Rightarrow> transBdd \<Rightarrow> bool"
  where
"pasDansBdd x []  = True" |
"pasDansBdd x (((c,m,i),b)#bdd) = (if(x = i) then False else pasDansBdd x bdd)"

fun export2 ::"transBdd \<Rightarrow> transaction list"
  where
"export2 [] = [] " |
"export2 (((c,m,i),(client,marchant,e))#xs) = 
  (if(e = valide \<and> (egOptOpt client marchant)) then ((c,m,i), getVal client)#export2 xs 
    else export2 xs) "

fun traiterMessagerListAux :: "message list \<Rightarrow> transBdd \<Rightarrow> transBdd"
  where
"traiterMessagerListAux [] bdd = bdd" |
"traiterMessagerListAux (x#xs) bdd = traiterMessagerListAux xs (traiterMessage x bdd)"

fun traiterMessagerList :: " message list \<Rightarrow>transBdd"
  where
"traiterMessagerList x = traiterMessagerListAux  x []"

value "traiterMessagerList [Ack (1, 0, 0) 1,Pay (1, 0, 0) 2]"
value "traiterMessagerList [Pay (1, 0, 0) 2, Ack (1, 0, 0) 1]"

value "traiterMessagerList [(Pay (1,2,3) 6),(Cancel (1,2,3))]"
value "traiterMessagerList [(Pay (0,0,0) 0)]"
value "traiterMessagerList [(Ack (0,0,0) 0)]"
value "traiterMessagerList [(Pay (0,0,0) 0),(Ack (0,0,0) 0)]"
value "traiterMessagerList [(Ack (0,0,0) 0),(Pay (0,0,0) 0)]"
value "export2 (traiterMessagerList [(Pay (1,1,0) 0),(Ack (1,1,0) 0)])"
value "export2 (traiterMessagerList [(Pay (0,0,0) 0)])"
value "traiterMessagerList [(Cancel (1,2,3)),(Cancel (1,2,4))]"
value "traiterMessagerList [(Pay (1,2,3) 6),(Cancel (1,2,3))]"
value "traiterMessagerList [(Pay (1,2,3) 6),(Ack (1,2,3) 0)]"
value "traiterMessagerList [(Pay (1,2,3) 0),(Ack (1,2,3) 1)]"
value "traiterMessagerList [(Pay (1,2,3) 1),(Ack (1,2,3) 0)]"
value "export2 (traiterMessagerList [(Pay (1,2,3) 1),(Ack (1,2,3) 0)])"
value "export2 (traiterMessagerList [(Ack (1,2,3) 0)])"
value "export2 (traiterMessagerList [(Pay (1,2,3) 0)])"
value "export2 (traiterMessagerList [(Pay (1,2,3) 6),(Cancel (1,2,3))])"
value "traiterMessagerList [(Pay (1,2,3) 6),(Ack (1,2,3) 0),(Pay(1,2,3) 7), (Ack (1,2,3) 8)]"
value "traiterMessagerList [(Cancel (1,2,3))]"

value "traiterMessage (Pay (1,2,3) 4) []"
value "traiterMessage (Ack (1,2,3) 4) [((1,2,3),(Some 4,None,progress))]"

value "traiterMessagerList [(Pay (1,2,3) 4),(Ack (1,2,3) 4)]"

fun search :: "transaction \<Rightarrow> transaction list \<Rightarrow> bool"
  where
"search _ [] = False "|
"search s (x#xs) = (if(s = x) then True else search s xs)"

value "search ((0,0,0),0) [] "
value "search ((1,2,3),4) [] "
value "search ((1,2,3),4) [((1,2,3),4),((1,2,3),5)] "
value "search ((1,2,6),4) [((1,2,3),4),((1,2,3),5)] "

fun isDoublon ::"transaction list \<Rightarrow> bool"
  where
"isDoublon [] = False" |
"isDoublon (x#xs) = (if(search x xs = False) then False else search x xs)"

value "isDoublon [((1,2,3),4),((1,2,3),5)]"
value "isDoublon [((1,2,3),4),((1,2,3),4)]"
value "isDoublon [((1,2,3),4)]"
value "isDoublon [((0,0,0),0),((0,0,0),0)]"
value "isDoublon []"

lemma un : " List.member(export2 (traiterMessagerList li)) ((c,m,i),n)  \<longrightarrow> n>0"
  quickcheck
  (*nitpick*)
  sorry

lemma deux : "\<not>isDoublon (export2 (traiterMessagerList li))"
  quickcheck
  (*nitpick*)
  sorry

value "traiterMessagerList [(Pay (1,2,3) 1),(Ack (1,2,3) 1),(Cancel (1,2,3))]"
value "traiterMessage (Cancel (1,2,3)) (traiterMessagerList [(Pay (1,2,3) 1),(Ack (1,2,3) 1)])"

lemma trois : "List.member (traiterMessagerList bdd) ((c,m,i),j, j,valide) \<longrightarrow>
              List.member (traiterMessage (Cancel (c,m,i)) (traiterMessagerList bdd)) ((c,m,i),j, j,annuler) "
  quickcheck
  (*nitpick*)
  sorry

lemma quatre :"List.member (traiterMessagerList bdd) ((c,m,i),j, j,annuler) \<longrightarrow>
              \<not>List.member (traiterMessagerList (bdd @[(Pay(c,m,i) m),(Ack(c,m,i) m)])) ((c,m,i),j, j,valide) "
  quickcheck
  (*nitpick*)
  sorry
 
value "traiterMessagerList [(Pay (0,0,0) 0),(Cancel (0,0,0))]"
value "traiterMessagerList [(Ack (1,2,3) 1),(Pay (1,2,3) 3),(Ack (1,2,3) 2)]"
lemma cinq : "x > 0 \<and> x \<ge> y \<and> y > 0 \<and>           
              List.member bdd (Pay (c,m,i) x) \<and>
              List.member bdd (Ack (c,m,i) y) \<and>
              \<not>List.member bdd (Cancel (c,m,i)) \<longrightarrow>
              List.member (export2(traiterMessagerList bdd)) ((c,m,i), x) "
  quickcheck
  (*nitpick*)
  sorry

value "traiterMessagerList [Ack (1, 0, 0) 1,Pay (1, 0, 0) 2]"
value "traiterMessagerList [Pay (1, 0, 0) 2, Ack (1, 0, 0) 1]"
value "export2 (traiterMessagerList [Pay (1, 0, 0) 2, Ack (1, 0, 0) 1])"
value "traiterMessagerList [Pay (1, 0, 0) 1, Ack (1, 0, 0) 1,Pay(0,0,0) 0]"
value "export2 (traiterMessagerList [Pay (1, 0, 0) 1, Ack (1, 0, 0) 1, Pay (0, 0, 0) 0])"

lemma six : "List.member (export2 (traiterMessagerList bdd)) ((c,m,i), x) \<longrightarrow>
              x>0\<and> y>0 \<and> x \<ge> y \<and>
             List.member bdd (Pay (c,m,i) x) \<and> 
             List.member bdd (Ack (c,m,i) y)  "
  quickcheck
  (*nitpick*)
  sorry

value "traiterMessagerList [Pay (0, 0, 0) 1,Ack (0,0,0) 1,Ack (0,0,0) 0]"
value "traiterMessagerList [Pay (0, 0, 0) 0, Pay (0, 0, 0) 1]"
value "traiterMessagerList [(Ack (1,2,3) 2),(Pay (1,2,3)1),(Pay (1,2,3)2)]"

value "traiterMessagerList [(Pay (1,2,3) 2)]"
value "traiterMessagerList [(Pay (1,2,3) 2),(Ack (1,2,3) 1)]"
value "traiterMessagerList [(Pay (1,2,3) 2),(Ack (1,2,3) 1),(Pay(1,2,3) 1)]"

value "traiterMessagerList [Pay (0, 0, 0) 0, Pay (0, 0, 0) 1]"
value "traiterMessagerList [Pay (0, 0, 0) 1, Pay (0, 0, 0) 0]"

value "traiterMessagerList [Ack (0, 0, 0) 2, Ack (0, 0, 0) 1]"
value "traiterMessagerList [Ack (0, 0, 0) 1, Ack (0, 0, 0) 2]"

value "traiterMessagerList [Pay (0, 0, 0) 0, Pay (0, 0, 0) 1, Ack (0, 0, 0) 0]"
value "traiterMessagerList [Pay (0, 0, 0) 0, Pay (0, 0, 0) 1, Ack (0, 0, 0) 0,Pay (0,0,0) 0]"

lemma septPay :"List.member bdd (Pay(c,m,i) x) \<longrightarrow> 
             x > y \<longrightarrow> 
             \<not>List.member (traiterMessagerList (bdd@[(Pay(c,m,i) y)])) ((c,m,i),Some y,Some z,progress)"
            
  quickcheck
  (*nitpick*)
  sorry

lemma septAck :"List.member bdd (Ack(c,m,i) x) \<longrightarrow> 
             x < y \<longrightarrow> 
             \<not>List.member (traiterMessagerList (bdd@[(Ack(c,m,i) y)])) ((c,m,i),Some y,Some z,progress)"
            
  quickcheck
  (*nitpick*)
  sorry

value "traiterMessagerList [Pay (0, 0, 0) 1, Ack (0, 0, 0) 2]"

value "traiterMessagerList [Pay (0, 0, 0) 2, Ack (0, 0, 0) 1]"
value "traiterMessagerList [Ack (0, 0, 0) 1, Pay (0, 0, 0) 2]"


value "traiterMessagerList [Pay (0, 0, 0) 1, Ack (0, 0, 0) 1,Pay (0, 0, 0)2]"
value "traiterMessagerList [Pay (0, 0, 0) 1, Ack (0, 0, 0) 1,Pay (0, 0, 0)2, Pay (0, 0, 0) 1]"

lemma huit : "List.member (export2 (traiterMessagerList(li))) ((c,m,i),n) \<longrightarrow> 
              List.member (export2 (traiterMessagerList(li @ li2))) ((c,m,i),x) \<longrightarrow>
               n = x"
  quickcheck
 (*nitpick*)
  sorry

lemma neuf :"List.member (export2 (traiterMessagerList l)) ((c,m,i), n) \<longrightarrow>
             List.member l (Pay (c,m,i) n)"
  quickcheck
 (*nitpick*)
  sorry

(* ----- Exportation en Scala (Isabelle 2018) -------*)

(* Directive d'exportation *)
export_code export2 traiterMessage in Scala



end

