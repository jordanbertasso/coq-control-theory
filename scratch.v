Require Import Floats.
Open Scope float_scope.

Definition semidef_pos_22 (x11 x12 x21 x22: float) :=
    forall (a b: float),
    a <> 0 /\ b <> 0 -> (
        (
            a * (a * x11 + b * x12)
            +
            b * (a * x21 + b * x22)
        ) <? 0) = false.



QMat_0 = mat_of_2x2_scalar(
    1.4849e3,-.0258e3,
    -.0258e3, 0.4061e3
);

QMat_1 = mat_mult(
    mat_mult(
        mat_of_3x2_scalar(1,0,0,
                            1,1,0),
        QMat_0

        https://www.wolframalpha.com/input?i=%7B%7Ba%2C+b%7D%2C+%7Bc%2C+d%7D%7D+*+%7B%7B1%2C+0%2C+0%7D%2C+%7B1%2C+1%2C+0%7D%7D
    ), 
    transpose(
        mat_of_3x2_scalar(1,0,0,
                            1,1,0)
                        --   1,1
                        --   0,1
                        --   0,0
    )
);

https://www.wolframalpha.com/input?i=%7B%7Ba+%2B+b%2C+b%2C+0%7D%2C+%7Bc+%2B+d%2C+d%2C+0%7D%7D+*+%7B%7B1%2C1%7D%2C+%7B0%2C+1%7D%2C+%7B0%2C+0%7D%7D