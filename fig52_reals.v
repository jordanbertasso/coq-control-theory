(* in_ellipsoid_Q?(n:posnat, Q:SquareMat(n), x:Vector[n]): bool =
    semidef_pos_22?(Q) AND
    symmetric_22?(Q) AND
    semidef_pos_22?(Block2M(M2Block(1,n,1,n)
        (I(1),transpose(V2Ml(n,x)),V2Ml(n,x),Q)))

ellipsoid_general: LEMMA
    FORALL (n:posnat,m:posnat, Q:SquareMat(n),
        M: Mat(m,n), x:Vector[n], y:Vector[m]):
            in_ellipsoid_Q?(n,Q,x)
            AND y = M*x
    IMPLIES
    in_ellipsoid_Q?(m,M*Q*transpose(M),y)

Let's define in_ellipsoid_Q? for 2x2 matrices

Need: semidef_pos_22, symmetric_22 and semidef_pos_33 (to represent the block matrix)

We don't need to check if the matrix is square because we are defining this on 2x2 matrices. *)
Require Import ZArith Reals.
Open Scope R_scope.

(* Control Theory Definitions *)

Definition semidef_pos_22 (x11 x12 x21 x22 : R) :=
    forall (a b : R),
    a <> 0 /\ b <> 0 -> 
        (a*(a*x11 + b*x12) + b*(a*x21 + b*x22)) >= 0.
    
Definition semidef_pos_33 (x11 x12 x13 x21 x22 x23 x31 x32 x33: R) :=
    forall (a b c : R),
    a <> 0 /\ b <> 0 /\ c <> 0 -> 
        (
        a * (a * x11 + b * x21 + c * x31)
        +
        b * (a * x12 + b * x22 + c * x32) 
        + 
        c * (a * x13 + b * x23 + c * x33)
        ) >= 0.

Definition symmetric_22 (x11 x12 x21 x22 : R) :=
    x12 = x21.

Definition in_ellipsoid_Q (q11 q12 q21 q22 : R) (x1 x2 : R) :=
    semidef_pos_22 q11 q12 q21 q22 /\
    symmetric_22 q11 q12 q21 q22 /\
    semidef_pos_33 1 x1 x2 x1 q11 q12 x2 q21 q22.

(* Useful Theorems *)

Theorem mul_neg_1_r : 
    forall x : R, x * -1 = -x.
Proof.
    Admitted.

Theorem mult_factor : 
    forall a b x y : R, a * (x + y) + b * (x + y) = (a + b) * (x + y).
Proof.
    intros.
    symmetry.
    set (x + y) as c.
    rewrite Rmul_comm.
    rewrite Rmult_plus_distr_l.
    set (c * b) as d.
    set (b * c) as e.
    Admitted.


(* semidef_pos_22 Examples *)

Example not_semidef_pos_22 : semidef_pos_22 (-1) (-1) (-1) (-1).
    Proof.
        unfold semidef_pos_22.
        intros.
        destruct H as [HA HB].
        rewrite mul_neg_1_r.
        rewrite mul_neg_1_r.
        Admitted.

Print Rsqr.

Theorem is_r_sqr (n : R) : n * n = Rsqr n.
Proof.
    Admitted.

        
Example is_semidef_pos_22: semidef_pos_22 1 1 1 1.
    Proof.
        unfold semidef_pos_22.
        intros.
        destruct H as [HA HB].
        rewrite Rmult_1_r.
        rewrite Rmult_1_r.
        rewrite mult_factor.
        set (a + b) as c.
        Admitted.
        (* rewrite Rle_ge.
        rewrite is_r_sqr.
        apply Rle_0_sqr. *)
        

Example is_semidef_pos_22_b: semidef_pos_22 1 2 2 1.
Proof.
    Admitted.

(* semidef_pos_33 Examples *)

Example is_semidef_pos_33 : semidef_pos_33 1 1 1 1 1 1 1 1 1.
    unfold semidef_pos_33.
    intros.
    destruct H as [HA [HB HC]].
    rewrite Rmult_1_r.
    rewrite Rmult_1_r.
    rewrite Rmult_1_r.
    rewrite mult_factor.
    rewrite mult_factor.
    set (a + b + c) as d.
    Admitted.
    (* rewrite Rle_ge.
    rewrite is_r_sqr.
    apply Rle_0_sqr. *)

(* ====================================================== *)
(* ====================================================== *)
(* ====================================================== *)



Example is_symmetric_22: symmetric_22 1 1 1 1.
Proof.
    unfold symmetric_22.
    reflexivity.
    Qed.

Example this_is_not_symmetric_22 : ~ symmetric_22 1 2 1 1.
Proof.
    unfold symmetric_22.
    apply not_eq_sym.
    apply Rlt_not_eq.
    replace 2 with (1+1).
    apply Rlt_plus_1.
    auto.
    Qed.


Example is_in_ellipsoid_Q :
    in_ellipsoid_Q 1 1 1 1 1 1.
Proof.
    unfold in_ellipsoid_Q.
    split.
    apply is_semidef_pos_22.
    split.
    apply is_symmetric_22.
    apply is_semidef_pos_33.
    Qed.