Require Import Arith.





(******************************************************************************)
(* FONCTIONS RECURSIVES ET INDUCTION SUR LES LISTES                           *)
(******************************************************************************)

(* On définit les listes de nat *)
Inductive nlist : Set :=
| nnil : nlist                  
| ncons : nat -> nlist -> nlist. 

(* ... avec des notations confortables *)
Infix "::" := ncons.
Notation "[]" := nnil.

(* Exercice *)
(* Définir "concat" la fonction de concaténation de deux listes l1 et l2 (par récursion sur l1) *)
Fixpoint concat (l1 l2 : nlist) : nlist := 
  match l1 with
  | []     => l2
  | x :: l => x::(concat l l2)
  end.

(* On note ++ en notation infix pour la concatenation *)
Infix "++" := concat.


(* On reprend la fonction appartient du TP de LIFLF *)

Fixpoint appartient (x : nat) (l : nlist) : bool :=
  match l with
  | [] => false
  | h::rl => (Nat.eqb x h) || (appartient x rl)
  end.
(* END CUT *)

(* Exprimer (cf. TD de LIFLC) et montrer que cette fonction retourne
true sur la donnée de paramètres x de type nat et l de type nlist
seulement si on peut écrire l comme une nlist l1 concaténée à une
nlist l2 commençant par x *)

(* on aura besoin du théorème 
   - Bool.orb_prop 
*)
Check Bool.orb_prop.

(* on aura besoin du théorème 
   - beq_nat_true (déjà vu)
*)

Check beq_nat_true.

(* En hypothèse l'existentiel est éliminé avec destruct de l'hypothèse *)
(* Rappel : la règle d'introduction de l'existentiel dans le but est exists objet_specialisé *)



Theorem appartient_seulement : forall(x:nat), forall(l:nlist), appartient x l = true -> exists(l1:nlist), exists(l2:nlist), l = concat l1 (x::l2).
Proof.
intro x.
intro l.
induction l.
-
intro h0.
exists [].
exists [].
discriminate.
-intro h1.
exists [].
exists l.
simpl.
destruct IHl.
+rewrite <- h1.
simpl.
rewrite <- h1.
Qed.

    
(**********************************************************************)
(* Exprimer et montrer que la fonction plus est commutative                       *)
(* On commencera par montrer un petit lemme technique                 *)
(**********************************************************************)

Lemma plus_Succ_r : forall a b, S (plus a b) = plus a (S b). 
Proof.
Admitted. (* remplacer ici *)

Lemma plus_commute : 
Proof.
Admitted. (* remplacer ici *)


(******************************************************************************)
(* Les arbres binaires de nat *)
(******************************************************************************)

(* le type inductif *)
Inductive BinTree : Set :=
  | leaf : BinTree 
  | node : BinTree -> nat -> BinTree -> BinTree.

(**********************************************************************)
(* Montrer par induction sur Bin E qu'un arbre binaire comportant
   n occurrences de l’arbre vide contient n - 1 éléments              *)
(**********************************************************************)
(* on aura sans doute besoin du théorème plus_n_Sm *)
Check plus_n_Sm.

(* les deux fonctions qui comptent *)
Fixpoint count_leaves (t:BinTree) : nat :=
end.

Fixpoint count_nodes (t:BinTree) : nat :=
end.

(* la propriété *)
Lemma count_leaves_nodes : forall (t:BinTree), 1 + (count_nodes t) =  (count_leaves  t).
Proof.
Admitted. (* remplacer ici *)


(**********************************************************************)
(* ÉTUDE DE CAS.

On se propose de regarder le cas de l'automate qui reconnaît les mots finissant par "aab".
On commence par définir cet automate en utilisant le TP de LIFLF.
 *)
(**********************************************************************)

(* inclure ici le TP de LF *)


(* Automate qui reconnaît les mots qui finissent par "aab" *)
Definition gaab := [ ]. (* remplacer ici *)

Definition Aaab := false. (* remplacer ici *)


(* Écrire en commentaire la grammaire régulière produisant le langage de l'automate *)
(* Source : X1
 *)

(* On peut définir le prédicat "être généré par cette grammaire" *)

(* En effet : une règle "N -> c M" signifie qu'un mot généré depuis N
   peut être constitué d'un c suivi par un mot généré depuis M donc
   pour tout mot w, le mot cw est généré par N si w est généré par M.
   Dit autrement : "pour tout mot w, si w est généré depuis M alors cw
   est généré depuis N".  C'est exactement ce qu'on se propose
   d'écrire. *)

(* On va donc définir un prédicat *inductif*, paramétré par un mot et
un état (vu comme un non terminal de la grammaire ), dont chaque
règle de construction caractérise chaque règle de grammaire *)

(* Définir ce prédicat inductif Paab, de type liste Alphabet -> nat -> Prop *)
Inductive Paab : list Alphabet -> nat -> Prop := False (* remplacer ici *)
.


(* Pour montrer qu'un mot est bien généré depuis un état, il suffit
d'appliquer (apply) les règles de construction jusqu'à tomber sur un
cas de base. *)
(* Montrer que le mot abaaab est bien généré depuis le non terminal 1 *)

Lemma exemple :  Paab [a;b;a;a;a;b] 1.
Proof.
Admitted. (* remplacer ici *)

(* CE PRÉDICAT (DÉRIVÉ DE LA GRAMMAIRE) CARACTÉRISE-T-IL BIEN LES MOTS
RECONNUS PAR L'AUTOMATE ? *)

(* Pour le montrer on va poser un lemme intermédiaire *)

(* Ce lemme, appelons-le PmimeA, énonce que pour tout mot généré à
partir d'un état/non terminal, disons q, de la grammaire, la lecture
de ce mot depuis q dans l'automate aboutit à un état, disons e, et cet
état e est acceptant. *)

(* Définir le lemme PmimeA *)
Lemma PmimeA : False. (* remplacer ici *)
Proof.
Admitted. (* remplacer ici *)

(* Pour le montrer une nouvelle tactique va être bien utile :
inversion.
  - La tactique "inversion" appliquée à un nom d'inductif énumère les
  cas *possibles* de règles qui ont pu le produire.
  - Les cas absurdes sont éliminés, en particulier si une hypothèse n'a
  pu apparaître qu'à l'aide de cas absurdes, le but est prouvé.
  - On va se servir de cette tactique pour se placer dans les différents
  cas du prédicat. *)



(* Énoncer et montrer le théorème principal : tout mot généré depuis le non terminal 1 est reconnu par l'automate. *)
Theorem PA : False. (* remplacer ici *)
Proof.
Admitted. (* remplacer ici *)

