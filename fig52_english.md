







What does `semidef_pos?(Block2M(M2Block(1,n,1,n) (I(1),transpose(V2Ml(n,x)),V2Ml(n,x),Q)))` mean?

It's a check to see if a matrix X is positive semi definite.
Where X is a block matrix (A C) where A = 1, B = transpose((x_1, x_2, ..., x_n)), C = (x_1, x_2, ..., x_n), D = Q
                          (B D)

```
M2Block(1,n,1,n)
m = 1
n = n
p = 1
q = n

A = Mat(1, 1)
B = Mat(n, 1)
C = Mat(1, n)
D = Mat(n, n)

rows1 = 1
rows2 = n
cols1 = 1
cols2 = n

[A C]
[B D]

[1x1 1xn]
[nx1 nxn]

[a_1_1, c_1_1, c_1_2, ..., c_1_n]
[b_1_1, d_1_1, d_1_2, ..., d_1_n]
[b_2_1, d_2_1, d_2_2, ..., d_2_n]
[...  , ...  , ...  , ..., ...  ]
[b_n_1, d_n_1, ...  , ..., d_n_n]

[1_1, ..., 1_n]
[2_1, ..., 2_n]
[..., ..., ...]
[]


---

Definition - in_ellipsoid_Q?

in_ellipsoid_Q?(n: postnat, Q: SquareMat(n), x: Vector[n]): bool = 
    true if:
        - Q is positive semi-definite
        - Q is symmetric
        - A is positive semi-definite
    where:
        A = [1             , ...x]
            [tranpose(...x), ...Q]


where n is a natural number, Q is a n by n matrix, x is a length n vector.

---

Lemma - ellipsoid_general

for all:
    - natural numbers n and m,
    - square matrices Q,
    - m by n matrices M
    - length n vectors x
    - length m vectors m

if true:
    - in_ellipsoid_Q(n, Q, x)
    - y = M * x
implies:
    - in_ellipsoid_Q(m, M * Q * transpose(M), y)
