Require Import Arith.
Require Import List.
Export ListNotations.


(* Fonction "lgr" qui calcule la longueur d'une liste de nat (et donc de type list nat) *)
Fixpoint lgr (l : list nat) : nat :=
match l with
|[] => 0
|n::l' => 1+ lgr l'
end.

Example ex_lgr : (lgr (1::2::3::4::5::[])) = 5.
Proof. simpl. reflexivity. Qed.

(* Fonction "mir" qui calcule le miroir d'une liste de nat *)
Fixpoint mir (l : list nat) : list nat :=
match l with 
|[] => []
|n::l' => (mir l')++[n]
end.
(* dans la vraie vie on ne fera jamais de concaténation de ce type mais ce n'est pas le problème ici *)

Example ex_mir : (mir (1::2::3::4::5::[])) = 5::4::3::2::1::[].
Proof. simpl. reflexivity. Qed.

(* On rappelle le type "btree" des arbres binaires avec valeurs de type nat stockées dans les feuilles *)
Inductive btree : Type :=
| F : nat -> btree
| N : btree -> btree -> btree
.

(* Fonction "bsumval" qui calcule la somme des valeurs contenues dans l'arbre *)
Fixpoint bsumval (ab : btree) : nat :=
match ab with
|F n => n
|N abG abD => bsumval abG + bsumval abD
end.

(* Fonction "bajout" qui ajoute un élément dans un arbre *)
(* plusieurs solutions sont possibles... *)
Fixpoint bajout (x : nat) (ab : btree) : btree :=
match ab with 
|F n => N (F n) (F x)
|N abG abD => N abG (bajout x abD)
end.

(* exemples *)
(* on peut définir "ab1" :  o
                           / \
                          o   2
                         / \
                        1   o
                           / \
                          o   3
                         / \
                        4   5
*)

Definition ab1 := N (N (F 1) (N (N (F 4) (F 5)) (F 3))) (F 2).

Example ex_bsumval_ab1 : (bsumval ab1) = 15.
Proof. cbv. reflexivity. Qed.

(*************** LOGIQUE CLASSIQUE ***************)

Context (E H G : Prop).

(* EXERCICE *)
(* Prouver les lemmes suivants *)
Lemma LC1 : ((H \/ E) -> G) -> ((E -> G) /\ (H -> G)).
Proof.
intro h0.
split.
-intro h1.
apply h0.
right.
assumption.
-intro h1.
apply h0.
left.
assumption.
Qed.


Lemma LC2 : (H \/ E) -> ((E -> H) -> H).
Proof.
intro h0.
intro h1.
destruct h0 as [h01 | h02].
-assumption.
-apply h1.
assumption.
Qed.


(* EXERCICE *)
(* Exprimer et montrer que la longueur de la concaténation de deux listes de nat (donc de type list nat)  est la somme des longueurs des concaténés*)
Lemma concat_compat (l1 : list nat) (l2 : list nat) : lgr (l1++l2) = lgr l1 + lgr l2.
Proof.
induction l1 as [ | n].
-simpl.
reflexivity.
-simpl.
rewrite <- IHl1.
reflexivity.
Qed.

(* EXERCICE *)
(* Montrer que la longueur d'une liste c'est la longueur de son miroir *)
(* On pourra avoir besoin de la commutativité de l'addition, donnée par le lemme Nat.add_comm, et dulemme précédent *)

Check Nat.add_comm.

Lemma lgrmireq (l : list nat) : lgr l = lgr (mir l).
Proof.
induction l as [ | n].
-simpl.
reflexivity.
-pose (concat_compat (mir l) [n]) as h0.
pose (Nat.add_comm 1 (lgr (mir l))) as h1.
simpl.
rewrite -> h0.
simpl.
rewrite <- h1.
rewrite -> IHl.
reflexivity.
Qed.

(* EXERCICE *)
(* Exprimer et montrer que l'addition est associative, c'est-à-dire qu'on a (x + y) + z = x + (y + z) pour x, y et z de type nat. *)
(* rappel : ce qui est noté x + y + z (sans parenthèses) est en fait (x + y) + z *)
Lemma p_assoc (x : nat) (y : nat) (z : nat) : (x + y) + z = x + (y + z).
Proof.
induction x as [ | x'].
-simpl.
reflexivity.
-simpl.
rewrite -> IHx'.
reflexivity.
Qed.


(* EXERCICE *)
(* Exprimer et montrer que la somme des valeurs d'un arbre t à laquelle on additionne un nat e est égale à la somme des valeurs de l'arbre t dans lequel on a ajouté un élément de valeur e. *)

(* On pourra avoir besoin de la commutativité de l'addition, donnée par le lemme Nat.add_comm, et de l'associativité démontrée auparavant. *)

Check Nat.add_comm.

Lemma bsumcons_compat (t : btree) (e : nat) : (bsumval t) + e = bsumval (bajout e t).
Proof.
induction t as [ | tG hG tD hD].
-simpl.
reflexivity.
-simpl.
pose (p_assoc (bsumval tG) (bsumval tD) e) as h0.
rewrite <- hD.
rewrite -> h0.
reflexivity.
Qed.


