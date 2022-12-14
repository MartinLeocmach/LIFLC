Require Import Arith.


(* AVOIR SON COURS SOUS LES YEUX *)
(* AVOIR SON COURS SOUS LES YEUX *)
(* AVOIR SON COURS SOUS LES YEUX *)
(* AVOIR SON COURS SOUS LES YEUX *)
(* AVOIR SON COURS SOUS LES YEUX *)


(**********************************************************************)
(* Un prédicat particulier : =                                        *)
(**********************************************************************)
(* Un prédicat = est déjà défini en Coq. On peut considérer qu'il s'agit de la plus petite relation réflexive *)
(* C'est un inductif avec une seule règle de construction : pour tout x on construit  x=x. *)
(* La règle d'introduction de = est "reflexivity". *)

Lemma egalite : 4=4.
Proof.
reflexivity.
Qed.

(* Lorsqu'on a une ÉGALITÉ x = y dans une hypothèse, disons Heq, on peut remplacer
- dans le but
  + tous les x libres par des y avec
    rewrite -> Heq.
  + tous les y libres par des x avec
    rewrite <- Heq.
- dans une hypothèse, disons H,
  + tous les x libres par des y avec
    rewrite -> Heq in H.
  + tous les y libres par des x avec
    rewrite <- Heq in H.
 *)

Lemma ex_rewrite (x : nat)  : 1 + (x + 3) = 6 -> 1 + (x + 3) = 1 + x + 3  -> 1 + (1 + x + 3) = 1 + 6.
Proof.
intro.
intro.
rewrite <- H.
rewrite -> H0.
reflexivity.
Qed.

(* En Coq des CONSTRUCTEURS DIFFÉRENTS donnent des TERMES DIFFÉRENTS.  *)
(* Si en hypothèse on trouve le prédicat d'égalité avec deux membres différents alors on peut achever la preuve directement avec
"discriminate". *)
Lemma hyp_egal_diff : 3=4 -> False.
Proof.
(* cette formule vient de l'introduction de la flèche *)
intro Habs.
(* on voit que l'hypothèse Habs est une égalité avec deux constructeurs différents, on finit la preuve directement avec "discriminate". *)
discriminate.
Qed.


(**********************************************************************)
(* STRUCTURE DE BASE DES LISTES (FINIES) D'ENTIERS                    *)
(**********************************************************************)


(*On rappelle que les objets de type nat sont définis inductivement de façon similaire à 
Inductive entiers : Set :=
  | O : entiers
  | S : entiers -> entiers.
*)

Print nat.

(* On dispose donc d'un principe d'induction nat_ind, construit à peu près comme vu en cours *)
Check nat_ind.
(* Si on omet le "forall P" qui n'est PAS du premier ordre, on se retrouve bien avec deux branches :
   - une branche qui demande de prouver sur le cas de base des nat, c'est-à-dire 0
   - une branche qui demande de prouver sur un nat construit par S à partir d'un nat sur lequel on sait déjà prouevr la propriété
   On peut en déduire la propriété sur tout nat obtenu par 0 et S. *)



(* EN COQ : l'application de la tactique "induction" sur un nom
   d'entier produira donc DEUX sous-buts (il y a bien 2 règles de
   construction des entiers...) :
  - Le sous-but correspondant au cas de bas O, 
  - Le sous-but correspondant au cas inductif où l'hypothèse d'induction apparaît
    dans le contexte.

COMME ON SAIT que ça va mettre deux nouvelles choses dans la branche de droite et rien de nouveau dans celle de gauche on peut même nommer directement :
   induction "n" as [ | "m" "Hyp_Ind_m"].
où n est dans le cas de droite l'entier S m avec comme hypothèse d'induction que la propriété est vraie pour m (hypothèse nommée ici Hyp_Ind_m).  
 *)


(* On définit les listes de nat *)
Inductive nlist : Set :=
| nnil : nlist                  
| ncons : nat -> nlist -> nlist. 

(* ... avec des notations confortables *)
Infix "::" := ncons.
Notation "[]" := nnil.

(* Vous avez vu la génération des principes d'induction ? *)
Check nlist_ind.
(* C'est tout à fait similaire au cas des nat.
   Si on omet le "forall P" qui n'est PAS du premier ordre, on se retrouve bien avec deux branches :
   - une branche qui demande de prouver sur le cas de base des listes
   - une branche qui demande de prouver sur une liste construite par :: à partir d'une liste sur laquelle on sait déjà prouevr la propriété
   On peut en déduire la propriété sur toute liste obtenue par [] et ::. *)





(******************************************************************************)
(* FONCTIONS NON-RECRUSIVES SUR LES TYPES INDUCTIFS                           *)
(******************************************************************************)

(* Si on n'a pas besoin d'hypothèse d'induction, il est en général suffisant de faire une étude par cas, 
   c'est-à-dire un destruct de l'objet étudié *)

Inductive Alphabet : Type :=
| a : Alphabet
| b : Alphabet.

(* Prouvez les correction et complétude de la fonction comp_alphabet de votre TP de LIFLF, c'est-à-dire qu'elle retourne true si et seulement si ses deux paramètres sont égaux
  - on procède par cas sur les deux paramètres
  - on peut être amené à faire des calculs (avec simpl dans le but ou simpl in toto dans l'hypothèse toto. *)
Definition comp_alphabet (x : Alphabet) (y : Alphabet) : bool := (* mettez votre code ici *)
match (x, y) with
| (a,a) => true
| (b, b) => true
| _ => false
end.


Theorem comp_alphabet_ssi (x : Alphabet) (y : Alphabet) : (comp_alphabet x y = true -> x = y) /\ (x = y -> comp_alphabet x y = true).
Proof.
split.
-intro h0.
induction x as [a | b].
induction y as [a | b].
reflexivity.
discriminate.
induction y as [a | b].
discriminate.
reflexivity.
-intro h0.
induction x as [a | b].
induction y as [a | b].
reflexivity.
discriminate.
induction y as [a | b].
discriminate.
reflexivity.
Qed.



(* On rappelle la fonction de comparaison sur les option nat codée en LIFLF *)
Definition comp_option_nat (x y: option nat) : bool :=
match (x, y) with
| (None, None) => true
| (None, Some m) => false
| (Some m, None) => false
| (Some m, Some n) => Nat.eqb m n
end.


(* EN COQ : si on a une hypothèse H : forall x, P(x) on peut la
 spécialiser en une nouvelle hypothèse pour une certaine valeur de x,
 disons n. Pour celà on invoque "pose (H n) as nouveauH".  On crée
 alors une nouvelle hypothèse qui s'appelle nouveauH qui est un cas
 particulier de H, celui où x vaut n : nouveauH : P(n)
*)


(* Montrer que (comp_option_nat x y) retourne true SEULEMENT SI x=y. 
   on utilisera le théorème
   beq_nat_true: forall n m : nat, Nat.eqb n  m = true -> n = m 
   qu'on spécialisera aux bons paramètres "n_fixe", "m_fixe" avec 
   pose (beq_nat_true "n_fixe" "m_fixe") as "nom_de_la_nouvelle_hypothèse".
   
  ATTENTION : Nat.eqb e1 e2 s'écrit aussi e1 =? e2

*)
Theorem comp_option_nat_seulement_si (x : option nat) (y : option nat) : comp_option_nat x y = true -> x = y.
Proof.
induction x.
-induction y.
+intro h0.
pose (beq_nat_true a0 a1) as h1.
destruct h1.
rewrite <- h0.
reflexivity.
reflexivity.
+intro h0.
discriminate.
-induction y.
+intro h0.
pose (beq_nat_true a0) as h1.
discriminate.
+intro h0.
reflexivity.
Qed.



(******************************************************************************)
(* FONCTIONS RECURSIVES ET INDUCTION SUR LES ENTIER                           *)
(******************************************************************************)

(* Exercice : montrer que la fonction plus appliquée à 0 et un x quelconque retourne x. *)
(* La définition de plus est récursive sur le paramètre de gauche, donc pas de problème ici, c'est juste un calcul (simpl) *)
Lemma plus_Z_l (x : nat) : plus 0 x = x.
Proof.
simpl.
reflexivity.
Qed. 

(* Exercice : montrer que la fonction plus appliquée un x quelconque et 0 retourne x. *)
(* Mmmh là il faut travailler par induction sur x... *)
(* on utilise "induction x as..." qui invoque la règle nat_ind. *)
Lemma plus_Z_r (x : nat) : plus x 0 = x.
Proof.
induction x as [ | n].
-reflexivity.
-simpl.
rewrite -> IHn.
reflexivity.
Qed. 



(******************************************************************************)
(* FONCTIONS RECURSIVES ET INDUCTION SUR LES LISTES                           *)
(******************************************************************************)

(* Exercice *)
(* Définir "concat" la fonction de concaténation de deux listes l1 et l2 (par récursion sur l1) *)
Fixpoint concat (l1 l2 : nlist) : nlist := (* écrire votre code ici *)
  match l1 with
  | [] => l2
  | n::l11 => n::(concat l11 l2)
  end.

(* On note ++ en notation infix pour la concatenation *)
Infix "++" := concat.

(* VU EN COURS : fonction de longueur des listes                              *)
Fixpoint length (l : nlist) : nat :=
  match l with
  | []     => 0 
  | x :: l => S(length l) 
  end.

(* Exercice : montrer que la fonction retourne 0 SEULEMENT SI la liste
   est vide *)
Lemma length_zero_seulement_si_vide (l : nlist) : length l = 0 -> l=[].
Proof.
intro h0.
induction l as [ | n l1].
-reflexivity.
-destruct IHl1.
+rewrite <- h0.
discriminate.
+discriminate.
Qed.



(* Exercice : montrer que la fonction appliquée à la concaténation de
deux listes quelconques l1 l2 retourne la somme des applications de
cette fonction à chacune des deux listes.*)
Lemma length_of_concat (l1 : nlist) (l2 : nlist) : length (l1 ++ l2) = length l1 + length l2.
Proof.
induction l1 as [ | l10 H1].
-simpl.
reflexivity.
-simpl.
rewrite -> IHH1.
reflexivity.
Qed.



(* QUANTIFICATION UNIVERSELLE *)
(* Règle d'introduction du quantificateur universel *)
(* La tactique utilisée pour la règle d'introduction de l'universel est intro "nom de la variable générique". *)

(* Prouver que pour tout nat x et toute liste de nat l,
la liste vide n'est pas obtenue par l'ajout de x en tête de l. *)
Lemma nil_neq_cons : forall (x:nat), forall (l:nlist), [] = x :: l -> False.
Proof.
  intro un_element_general.
  intro une_liste_generale.
  intro Habsurde.
    (* poursuivre la preuve *)
  discriminate.
Qed.



(* Exprimer et montrer que pour tout élément x et toutes listes l1 et
l2, ajouter x en tête de la concaténation de l1 et l2 est
la même chose que concaténer l1 avec x en tête et l2. *)
(* pas de difficulté, c'est juste un pas de calcul (simpl). *)

Lemma concat_cons : forall (x:nat), forall (l1:nlist), forall (l2:nlist), concat (x::l1) l2 = x::concat l1 l2 -> True.
Proof.
intro x.
intro l1.
intro l2.
simpl.
reflexivity.
Qed.

(* Eprimer et montrer maintenant que pour toute liste l1, concaténer à l1 la liste vide renvoie exactement la liste l1. *)
(* Comme on a défini concat par récursion sur le premier paramètre, il va falloir une induction... *)
Lemma concat_nil_r : forall (l1:nlist), concat l1 [] = l1 -> True.
Proof.
induction l1 as [ | l10 H1].
-simpl.
reflexivity.
-simpl.
reflexivity.
Qed.

