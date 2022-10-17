(* LES SEULES COMMANDES AUTORISÉES SONT CELLES DÉCRITES DANS CE FICHIER. *)

(* Les indications entre  ne sont pas à recopier, elles indiquent
   juste que vous avez à mettre un nom à cet endroit. *)


(* On introduit les variables propositionnelles avec lesquelles 
   on va travailler par la suite *)
Context (P Q R A Z J F M S T: Prop).

(**********************************************************************)
(* Exercice 1 LA FLÈCHE  ***********************)
(* - axiome : assumption
   - introduction de la flèche : intro "nom qu'on donne à l'hypothèse" 
   - élimination de la flèche : apply "nom de l'hypothèse utilisée" *)
Theorem exercice_1a: P -> (P -> Q) -> Q.
Proof.
intro h0.
intro h1.
apply h1.
assumption.
Qed.


Theorem exercice_1b: (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
intro h0.
intro h1.
intro h2.
apply h1.
apply h0.
assumption.
Qed.

(* Exercice 2 LE ET  ***********************)
(* Une variante de la question précédente avec /\ *)
(* - décomposition du /\ en hypothèse : destruct "nom de l'hypothèse avec /\" as [ "nom gauche" "nom droite" ]
*)
Theorem exercice_2a: (P -> Q) /\ (Q -> R) -> (P -> R).
Proof.
intro h0.
destruct h0 as [h01 h02].
intro h1.
apply h02.
apply h01.
assumption.
Qed.

(* - introduction du /\ : split *)
(* On obtient bien deux sous-buts *)
Theorem exercice_2b : P -> Q -> P /\ Q.
Proof.
intro h0.
intro h2.
split.
-assumption.
-assumption.
Qed.
  
(* Exercice 3 LE OU  ***********************)
(* introduction du ou :
   - depuis la droite : right
   - depuis la gauche : left

   decomposition du \/ en hypothèse : destruct "nom de l'hypothèse avec \/" as [ "nom gauche" | "nom droite" ]
   notez le | qui sépare les sous-buts. *)

Theorem exercice_3a: (P \/ Q) -> (Q \/ P).
Proof.
intro h0.
destruct h0 as [h01 | h02].
-right.
assumption.
-left.
assumption.
Qed.

(* À partir de maintenant on nommera SYSTÉMATIQUEMENT les hypothèses qui
apparaissent dans les destruct avec "as" et suivant le nombre de sous-buts *)
(* ---------------------------------------------------------------------*)


(* zéro constructeur *)
Print False. 
(* un seul constructeur car une seule règle d'intro *)
Print and.
(* deux constructeurs car deux règles d'intro*)
Print or.  

(* destruct donne bien un sous but par constructeur *)
(* On remarque que comme False n'a aucun constructeur : le destruct
résoud le but *)
Theorem ex_falso_quodlibet : False ->  P.
Proof.
intro h0.
destruct h0.
Qed.

(** un peu difficile **)
(* Plus généralement, la tactique exfalso remplace tout but par False. *)
(* Si on peut déduire False des hypothèses, c'est alors gagné ! *)

Theorem ex_falso_quodlibet_Q : (A -> False) -> A -> (P \/ (Q -> Z /\ J) -> F).
Proof.
intro h0.
intro h1.
destruct h0.
assumption.
Qed.
  

(* ---------------------------------------------------------------------*)


(* Exercice 4 PREMIÈRE MODÉLISATION  ***********************)
(* Modéliser l'exercice de TD "Zoé va à Paris", prouver que Zoé va à Paris *)
(* - introduction du /\ : split
*)
Theorem zoe_va_a_paris : (A /\ J -> Z) -> (J -> A) -> (Z \/ J) -> Z.
Proof.
intro H0.
intro H1.
intro H2.
destruct H2 as [H21 | H22].
-assumption.
-apply H0.
split.
apply H1.
assumption.
assumption.
Qed.

(* Exercice 5 LE NOT *************************)

(* - la notation not : unfold not
   - la notation not en hypothèse : unfold not in "nom de l'hypothèse avec le ~ "
*)
Theorem exercice_5a : (~P \/ ~Q) -> ~(P /\ Q).
Proof.
intro H0.
unfold not.
unfold not in H0.
intro H1.
destruct H1 as [H11 H12].
destruct H0 as [H01 | H02].
-apply H01.
assumption.
-apply H02.
assumption.
Qed.
(* on voit qu'on passe son temps à faire des unfold dans chacun des sous-buts, il aurait donc mieux valu *commencer* par ce unfold, avant l'introduction de la flèche *)


(* Si on a toto et ~toto dans les hypothèses, alors le but est résolu avec "contradiction." *)
(* c'est juste un raccourci pour exfalso. apply "hypothèse avec le -> False". assumption. *)
Theorem exercice_5b : P -> ~P -> Q.
Proof.
intro h0.
intro h1.
contradiction.
Qed.

(**********************************************************************)
(* Exercice 6 LE TIERS-EXCLU *)

(* On introduit la règle de tiers-exclu. *)
Context (Tiers_exclus: forall X: Prop, X \/ ~X).

(* Pour l'utiliser, c'est-à-dire pour avoir deux sous buts, un avec toto en hypothèse, l'autre avec ~toto, on invoquera :
   destruct (Tiers_exclus toto) as [ "nom_hyp" | "nom_hyp ~" ].
*)


Theorem exercice_6a: ((P -> Q) -> P) -> P.
Proof.
intro h0.
destruct (Tiers_exclus (P)) as [h11 | h12].
-assumption.
-apply h0.
intro h3.
contradiction.
Qed.

(* Deuxième modélisation *)
(* Modéliser l'exercice de TD "Frodon va au Mordor", prouver que Frodon est triste *)

Theorem exercice_6b : (~F -> S) -> (S -> T) -> (F -> ~A) -> (~A -> T) -> T.
Proof.
Qed.


(* Quid de ~~P et P ? *)
Theorem exercice_6c: (~~P -> P) /\ (P -> ~~P).
(* Pour l'un des deux sens on aura besoin du tiers-exclu et, en remarquant qu'on peut déduire False des hypothèses, de la simplification "exfalso". *)

Proof.
Qed.
