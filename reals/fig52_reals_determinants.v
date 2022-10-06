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
Require Import Psatz.
Require Import Reals Interval.Tactic.
Require Import Reals.
Open Scope R_scope.

(* Control Theory Definitions *)

Definition semidef_pos_22 (x11 x12 x21 x22 : R) :=
    forall (a b : R),
    a <> 0 \/ b <> 0 -> 
        (a*(a*x11 + b*x12) + b*(a*x21 + b*x22)) >= 0.

Definition semidef_pos_22_determinant (x11 x12 x21 x22 : R) :=
    x11 >= 0 /\ x11*x22 - x12*x21 >= 0.
    
Definition semidef_pos_33 (x11 x12 x13 x21 x22 x23 x31 x32 x33: R) :=
    forall (a b c : R),
    a <> 0 \/ b <> 0 \/ c <> 0 -> 
        (
        a * (a * x11 + b * x21 + c * x31)
        +
        b * (a * x12 + b * x22 + c * x32) 
        + 
        c * (a * x13 + b * x23 + c * x33)
        ) >= 0.

Definition semidef_pos_33_determinant (x11 x12 x13 x21 x22 x23 x31 x32 x33: R) :=
    x11 >= 0 
    /\ 
    x11*x22 - x12*x21 >= 0
    /\ 
    x11*(x22*x33 + (Ropp x23*x32)) + Ropp(x12*(x21*x33 + Ropp (x23*x31))) + x13*(x21*x32 + Ropp (x22*x31)) >= 0.

Definition symmetric_22 (x11 x12 x21 x22 : R) :=
    x12 = x21.

Definition in_ellipsoid_Q (q11 q12 q21 q22 : R) (x1 x2 : R) :=
    semidef_pos_22_determinant q11 q12 q21 q22 /\
    symmetric_22 q11 q12 q21 q22 /\
    semidef_pos_33_determinant 1 x1 x2 x1 q11 q12 x2 q21 q22.

Definition ellipsoid_general 
    (q11 q12 q21 q22 : R) (m11 m12 m21 m22 : R) (x1 x2 : R) (y1 y2 : R) :=
    in_ellipsoid_Q q11 q12 q21 q22 x1 x2 
    /\ 
    y1 = x1 * m11 + x2 * m21 /\ y2 = x1 * m12 + x2 * m22
    ->
    in_ellipsoid_Q m11 m12 m21 m22 y1 y2.

(* Useful Theorems *)

Theorem mul_neg_1_r : 
    forall x : R, x * -1 = -x.
Proof.
    intros.
    lra.
    Qed.

Theorem mult_factor :
    forall a b x y : R, a * (x + y) + b * (x + y) = (a + b) * (x + y).
Proof.
    intros.
    symmetry.
    set (x + y) as c.
    rewrite Rmult_comm.
    rewrite Rmult_plus_distr_l.
    set (c * b) as d.
    set (b * c) as e.
    assert (d = e). {subst d. subst e. rewrite Rmult_comm. reflexivity. }
    rewrite H.
    rewrite Rmult_comm.
    reflexivity.
    Qed.

Theorem is_r_sqr (n : R) : n * n = Rsqr n.
Proof.
    unfold Rsqr.
    reflexivity.
    Qed.

(* semidef_pos_22 Examples *)

Example not_semidef_pos_22 : ~ semidef_pos_22_determinant (-1) (-1) (-1) (-1).
Proof.
    unfold semidef_pos_22_determinant.
    nra.
    Qed.

Example not_semidef_pos_22_b: ~ semidef_pos_22_determinant 1 2 2 1.
Proof.
    unfold semidef_pos_22_determinant.
    nra.
    Qed.


Example is_semidef_pos_22: semidef_pos_22 1 1 1 1.
Proof.
    unfold semidef_pos_22.
    intros.
    rewrite Rmult_1_r.
    rewrite Rmult_1_r.
    rewrite mult_factor.
    set (a + b) as c.
    rewrite is_r_sqr.
    apply Rle_ge.
    apply Rle_0_sqr.
    Qed.

Example is_semidef_pos_22_determinant: semidef_pos_22_determinant 1 1 1 1.
Proof.
    unfold semidef_pos_22_determinant.
    split.
    nra.
    nra.
    Qed.


(* semidef_pos_33 Examples *)

Example is_semidef_pos_33 : semidef_pos_33 1 1 1 1 1 1 1 1 1.
    unfold semidef_pos_33.
    intros.
    rewrite Rmult_1_r.
    rewrite Rmult_1_r.
    rewrite Rmult_1_r.
    rewrite mult_factor.
    rewrite mult_factor.
    set (a + b + c) as d.
    nra.
    Qed.


(* symmetric_22 Examples *)

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

(* in_ellipsoid_Q Examples *)

Example is_in_ellipsoid_Q :
    in_ellipsoid_Q 1 1 1 1 1 1.
Proof.
    unfold in_ellipsoid_Q.
    split.
    unfold semidef_pos_22_determinant.
    nra.
    split.
    apply is_symmetric_22.
    unfold semidef_pos_33_determinant.
    nra.
    Qed.


(* Jobredeaux example - Figure 32 *)


(* /*@ logic matrix QMat_0 =mat_of_2x2_scalar(1.4849e3,-.0258e3,-.0258e3, 0.4061e3); *)


(* Goal forall a b : R, a <> 0 /\ b <> 0 ->
    Rsqr a * 1484.9 + Rsqr b * 406.1 >= a * b * 25.8.
Proof.
    intros.
    destruct H as [HA HB].
    unfold Rsqr.
    nra.
    Qed. *)


Example Figure_32 :
    in_ellipsoid_Q 1484.9 (-25.8) (-25.8) 406.1 0 0.
Proof.
    unfold in_ellipsoid_Q.
    split.
        - 
        unfold semidef_pos_22_determinant.
        intros.
        nra.
        - split.
            + 
            unfold symmetric_22.
            reflexivity.
            +
            unfold semidef_pos_33_determinant.
            nra.
    Qed.

(* Proof 
a * (a * 1484.9 + b * -25.8) + b * (a * -25.8 + b * 406.1) >= 0

a^2 * 1489.8 + 2*a*b*(-25.8) + b^2 * 406.1 >= 0

a^2 * 1489.8 + b^2 * 406.1 >= a*b*25.8 (trivial, think about what happens if a*b < 0) *)

Example Figure_32_2 :
    in_ellipsoid_Q 1484.9 (-25.8) (-25.8) 406.1 1 1.
Proof.
    unfold in_ellipsoid_Q.
    split.
        unfold semidef_pos_22_determinant.
        nra.
    split.
        -
            unfold symmetric_22.
            reflexivity.
        -
        unfold semidef_pos_33_determinant.
        nra.
    Qed.

(* Proof for in_ellipsoid_Q for controller state in range (0, 0) - (1, 1) *)

Theorem in_ellipsoid_Q_range (x1 x2 : R) :
    0 <= x1 <= 2 /\ 0 <= x2 <= 2 -> in_ellipsoid_Q 1484.9 (-25.8) (-25.8) 406.1 x1 x2.
Proof.
    intros.
    unfold in_ellipsoid_Q.
    split.
        - 
        unfold semidef_pos_22_determinant.
        nra.
        - split.
            + 
            unfold symmetric_22.
            reflexivity.
            +
            unfold semidef_pos_33_determinant.
            nra.
    Qed.

(* in_ellipsoid x1 x2 /\ sat y1 /\ sat y2 /\ z = do_controller x1 x2 y1 y2 matrix -> in_ellipsoid z *)
(* z is the result of the computation *)

(* # 1
x1 = 0
x2 = 0

-1 <= x1b <= 1
x2b = 0

---

# 2
-1 <= x <= 1
x2 = 0

-1 <= y <= 1

x1b = 0.499 * x1 + y
-0.499 - 1 <= x1b <= 0.499 + 1

x2b = 0.01 * x1 + x2
- 0.01 <= x2b <= 0.01

---

# 3
-0.499 - 1 <= x1 <= 0.499 + 1
- 0.01 <= x2 <= 0.01

x1b = 0.499 * x1 + y
0.499 * (-0.499 - 1) - 1 <= x1b <= 0.499 * (0.499 + 1) + 1

x2b = 0.01 * x1 + x2
0.01 * (-0.499 - 1) - 0.01 <= x2b <= 0.01 * (0.499 + 1) + 0.01

---

# 4
0.499 * (-0.499 - 1) - 1 <= x1 <= 0.499 * (0.499 + 1) + 1
0.01 * (-0.499 - 1) - 0.01 <= x2 <= 0.01 * (0.499 + 1) + 0.01 *)


(* Instead of receiving y and yd to calculate yc, we just input yc and saturate it *)
Theorem First_Iteration (x1 x2 yc x1b x2b : R): 
    (* xc = zeros(2,1); *)
    x1 = 0 /\ x2 = 0
    /\ 
    in_ellipsoid_Q 0.0006742 0.0000428 0.0000428 0.0024651 x1 x2
    /\ 
    -1 <= yc <= 1
    /\ 
    x1b = 0.499 * x1 - 0.05 * x2 + yc
    /\
    x2b = 0.01 * x1 + x2 (* x2b = 0*)
    (* \tilde P - Eqn 14 *)
    -> in_ellipsoid_Q 1483.48 (Ropp 25.7711) (Ropp 25.7711) 406.11 x1b x2b.
Proof.
Proof.
    intros.
    split.
        - 
        unfold semidef_pos_22_determinant.
        nra.
        - split.
            + 
            reflexivity.
            +
            split. nra.
            split.
            destruct H as [A [B [C [D [E F]]]]].
            nra.
            nra.
Qed.

(* Instead of receiving y and yd to calculate yc, we just input yc and saturate it *)
Theorem Second_Iteration (x1 x2 yc x1b x2b : R): 
    -1 <= x1 <= 1 /\ x2 = 0
    /\ 
    in_ellipsoid_Q 0.0006742 0.0000428 0.0000428 0.0024651 x1 x2
    /\ 
    -1 <= yc <= 1
    /\ 
    x1b = 0.499 * x1 - 0.05 * x2 + yc
    /\
    x2b = 0.01 * x1 + x2 (* x2b = 0*)
    (* \tilde P - Eqn 14 *)
    -> in_ellipsoid_Q 1483.48 (Ropp 25.7711) (Ropp 25.7711) 406.11 x1b x2b.
Proof.
Proof.
    intros.
    split.
        - 
        unfold semidef_pos_22_determinant.
        nra.
        - split.
            + 
            reflexivity.
            +
            split. nra.
            split.
            destruct H as [A [B [C [D [E F]]]]].
            nra.
            nra.
Qed.

(* Instead of receiving y and yd to calculate yc, we just input yc and saturate it *)
Theorem Third_Iteration (x1 x2 yc x1b x2b : R): 
    -0.499 - 1 <= x1 <= 0.499 + 1 /\ -0.01 <= x2 <= 0.01
    /\ 
    in_ellipsoid_Q 0.0006742 0.0000428 0.0000428 0.0024651 x1 x2
    /\ 
    -1 <= yc <= 1
    /\ 
    x1b = 0.499 * x1 - 0.05 * x2 + yc
    /\
    x2b = 0.01 * x1 + x2
    (* \tilde P - Eqn 14 *)
    -> in_ellipsoid_Q 1483.48 (Ropp 25.7711) (Ropp 25.7711) 406.11 x1b x2b.
Proof.
Proof.
    intros.
    split.
        - 
        unfold semidef_pos_22_determinant.
        nra.
        - split.
            + 
            reflexivity.
            +
            split. nra.
            split.
            destruct H as [A [B [C [D [E F]]]]].
            nra.
            nra.
Qed.

(* Instead of receiving y and yd to calculate yc, we just input yc and saturate it *)
Theorem Forth_Iteration (x1 x2 yc x1b x2b : R): 
    0.499*(-0.499 - 1) - 1 <= x1 <= 0.499*(0.499 + 1) + 1 /\ 0.01 * (-0.499 -1) - 0.01 <= x2 <= 0.01 * (0.499 + 1) + 0.01
    /\ 
    in_ellipsoid_Q 0.0006742 0.0000428 0.0000428 0.0024651 x1 x2
    /\ 
    -1 <= yc <= 1
    /\ 
    x1b = 0.499 * x1 - 0.05 * x2 + yc
    /\
    x2b = 0.01 * x1 + x2
    (* \tilde P - Eqn 14 *)
    -> in_ellipsoid_Q 1483.48 (Ropp 25.7711) (Ropp 25.7711) 406.11 x1b x2b.
Proof.
Proof.
    intros.
    split.
        - 
        unfold semidef_pos_22_determinant.
        nra.
        - split.
            + 
            reflexivity.
            +
            split. nra.
            split.
            destruct H as [A [B [C [D [E F]]]]].
            nra.
            nra.
Qed.

Theorem a (x1 x2 : R): 
    in_ellipsoid_Q 0.0006742 0.0000428 0.0000428 0.0024651 x1 x2
    ->
    -0.0259653615419 <= x1 <= 0.0259653615419
    /\
    -0.04962 <= x2 <= 0.04962.
Proof.
    intros.
    destruct H as [A [B [C1 [C2 C3]]]].
    split.
    nra.
Qed.


(* Will try to get x1 and x2 isolated in their own hypothesis *)
Theorem Loop (x1 x2 yc x1b x2b s : R): 
    in_ellipsoid_Q 0.0006742 0.0000428 0.0000428 0.0024651 x1 x2
    /\ 
    -1 <= yc <= 1
    /\
    (* This is implied in the hypothesis check notes.md *)
    -0.04962 <= x2 <= 0.04962
    /\
    (* This is already in the hypothesis from 1 * 0.0006742 - x1 * x1 >= 0. I just cant put it into this form. *)
    -0.0259653615419 <= x1 <= 0.0259653615419
    /\ 
    x1b = 0.499 * x1 - 0.05 * x2 + yc
    /\
    x2b = 0.01 * x1 + x2
    -> 
    (* \tilde P - Eqn 14 *)
    in_ellipsoid_Q 1483.48 (Ropp 25.7711) (Ropp 25.7711) 406.11 x1b x2b.
Proof.
    intros.
    destruct H as [A [B [D [E F]]]].
    unfold in_ellipsoid_Q in A.
    destruct A as [A1 [A2 A3]].
    unfold semidef_pos_33_determinant in A3.
    destruct A3 as [A31 [A32 A33]].
    split.
        unfold semidef_pos_22_determinant.
        nra.
        split.
        reflexivity.
        split.
        nra.
        split.
        rewrite Rmult_1_l.
        (* 
        It should be possible to prove the next statement

        1. -sqrt(0.0006742) <= x1 <= sqrt(0.0006742)
        2. aprox -0.05 <= x2 <= 0.05
        3. -1 <= yc <= 1

        0.499 * -sqrt(0.0006742) -0.05 * 0.05 - 1 <= x1b <= 0.499*sqrt(0.0006742) + 0.05 * 0.05 + 1
        ✅ - 1.01545671541 <= x1b <= 1.01545671541


        https://www.wolframalpha.com/input?i=0.0006742+*+0.0024651+-+0.0000428+*+0.0000428+-+x1+*+x1+*+0.0024651+-+0.0000428+*+x2+*+x1+%2B+x1+*+x2+*+0.0000428+-+0.0006742+*+x2+*+x2+%3E%3D+0%2C+-sqrt%280.0006742%29+%3C%3D+x1+%3C%3D+sqrt%280.0006742%29
        0.0006742 * 0.0024651 - 0.0000428 * 0.0000428 - x1 * x1 * 0.0024651  - 0.0000428 * x2 * x1 + x1 * x2 * 0.0000428  - 0.0006742 * x2 * x2 >= 0 *)
        nra.
        nra.
Qed.