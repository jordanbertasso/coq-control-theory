(* in_ellipsoid_Q?(n:posnat, Q:SquareMat(n), x:Vector[n]): bool =
    semidef_pos_22?(Q) AND
    symmetric?(Q) AND
    semidef_pos_22?(Block2M(M2Block(1,n,1,n)
        (I(1),transpose(V2Ml(n,x)),V2Ml(n,x),Q))) *)

(* ellipsoid_general: LEMMA
    FORALL (n:posnat,m:posnat, Q:SquareMat(n),
        M: Mat(m,n), x:Vector[n], y:Vector[m]):
            in_ellipsoid_Q?(n,Q,x)
            AND y = M*x
    IMPLIES
    in_ellipsoid_Q?(m,M*Q*transpose(M),y) *)

(* Now let's define in_ellipsoid_Q? for 2x2 matrices *)

(* Need: semidef_pos_22?, symmetric? and semidef_pos_22_block*)

(* semidef_pos_22?(A: (square?)): bool = FORALL (x: Vector[A`rows]): x*(A*x) >= 0 *)

(* We don't need to check if the matrix is square because we are defining this on 2x2 matrices*)
(* Check whether a*(a*x11 + b*x12) + b*(a*x21 + b*x22) is positive for all a and b *)

(* Prove that the sum of two nats greater than or equal to zero is also greater than or equal to zero *)
Theorem sum_ge_eq_zero (a b : nat) : 
    a + b >= 0.
Proof.
    unfold ge.
    intros.
    Admitted.


Require Import ZArith.
Open Scope Z_scope.


Theorem mul_neg_1_l : 
    forall x : Z, -1 * x = -x.
Proof.
    auto.
    Qed.

Theorem mul_neg_1_r : 
    forall x : Z, x * -1 = -x.
Proof.
    intros.
    unfold Z.opp.
    simpl.
    destruct x.
        - reflexivity.
        - simpl. apply fast_Zred_factor0. reflexivity.
        - simpl. apply fast_Zred_factor0. reflexivity.
    Qed.

(* Search (?x + ?y) inside Z. *)

Theorem join: forall x y, exists c, x + y = c.
Proof.
    intros.
    exists (x + y).
    reflexivity.
    Qed.

Theorem distrib_l : 
    forall a b x y : Z, a * (x + y) + b * (x + y) = (a + b) * (x + y).
Proof.
    intros.
    symmetry.
    set (x + y) as c.
    rewrite Z.mul_comm.
    rewrite Z.mul_add_distr_l.
    set (c * b) as d.
    set (b * c) as e.
    assert (d = e). subst d. subst e. rewrite Z.mul_comm. reflexivity.
    rewrite Z.mul_comm.
    rewrite H.
    reflexivity.
    Qed.

(* ====================================================== *)
(* ====================================================== *)
(* ====================================================== *)

Definition semidef_pos_22 (x11 x12 x21 x22 : Z) :=
    forall (a b : Z),
    a <> 0 /\ b <> 0 -> 
        (a*(a*x11 + b*x12) + b*(a*x21 + b*x22)) >= 0.
    

Example this_is_not_pos_semidef : semidef_pos_22 (-1) (-1) (-1) (-1).
    Proof.
        unfold semidef_pos_22.
        intros.
        destruct H as [HA HB].
        rewrite mul_neg_1_r.
        rewrite mul_neg_1_r.
        destruct a.
            - simpl. contradiction.
            - destruct b.
                + simpl. contradiction.
                + admit.
                + admit.
            - admit.
        Admitted.


(* Search (?x * ?x) inside Z. *)
(* Check Z.square_nonneg. *)

(* Search ( _ >= _) inside Z. *)
        
Example is_pos_semidef_22 : semidef_pos_22 1 1 1 1.
    Proof.
        unfold semidef_pos_22.
        intros.
        destruct H as [HA HB].
        rewrite Z.mul_1_r.
        rewrite Z.mul_1_r.
        rewrite distrib_l.
        set (a + b) as c.
        rewrite <- Z.square_spec.
        apply Z.le_ge.
        rewrite Z.square_spec.
        apply Z.square_nonneg.
        Qed.
        

Example this_is_semidef: semidef_pos_22 1 2 2 1.
Proof.
    Admitted.
    (* simpl. induction a. unfold semidef_pos_22.
    - simpl. induction b. 
        + unfold semidef_pos_22. auto.
        + simpl. replace (0 <> 0) with False. apply <>.
            + auto.
            - auto. *)
    
(* ====================================================== *)
(* ====================================================== *)
(* ====================================================== *)

Definition semidef_pos_33 (x11 x12 x13 x21 x22 x23 x31 x32 x33: Z) :=
    forall (a b c : Z),
    a <> 0 /\ b <> 0 /\ c <> 0 -> 
        (
        a * (a * x11 + b * x21 + c * x31)
        +
        b * (a * x12 + b * x22 + c * x32) 
        + 
        c * (a * x13 + b * x23 + c * x33)
        ) >= 0.

Example is_semidef_pos_33 : semidef_pos_33 1 1 1 1 1 1 1 1 1.
    unfold semidef_pos_33.
    intros.
    destruct H as [HA [HB HC]].
    rewrite Z.mul_1_r.
    rewrite Z.mul_1_r.
    rewrite Z.mul_1_r.
    rewrite distrib_l.
    rewrite distrib_l.
    set (a + b + c) as d.
    rewrite <- Z.square_spec.
    apply Z.le_ge.
    rewrite Z.square_spec.
    apply Z.square_nonneg.
    Qed.

(* ====================================================== *)
(* ====================================================== *)
(* ====================================================== *)

Definition symmetric (x11 x12 x21 x22 : Z) :=
    x12 = x21.

Example s_symmetric_22 : symmetric 1 1 1 1.
Proof.
    unfold symmetric.
    reflexivity.
    Qed.

(* Search (_ <> _) in Z. *)

Example this_is_not_symmetric : ~ symmetric 1 2 1 1.
Proof.
    unfold symmetric.
    apply Z.neq_sym.
    apply Z.lt_neq.
    reflexivity.
    Qed.

(* ====================================================== *)
(* ====================================================== *)
(* ====================================================== *)

(* in_ellipsoid_Q?(n:posnat, Q:SquareMat(n), x:Vector[n]): bool =
    semidef_pos_22?(Q) AND
    symmetric?(Q) AND
    semidef_pos_22?(Block2M(M2Block(1,n,1,n)
        (I(1),transpose(V2Ml(n,x)),V2Ml(n,x),Q))) *)

Definition in_ellipsoid_Q (q11 q12 q21 q22 : Z) (x1 x2 : Z) :=
    semidef_pos_22 q11 q12 q21 q22 /\
    symmetric q11 q12 q21 q22 /\
    semidef_pos_33 1 x1 x2 x1 q11 q12 x2 q21 q22.

Example is_in_ellipsoid_Q :
    in_ellipsoid_Q 1 1 1 1 1 1.
Proof.
    unfold in_ellipsoid_Q.
    split.
    apply is_pos_semidef_22.
    split.
    apply s_symmetric_22.
    apply is_semidef_pos_33.
    Qed.
