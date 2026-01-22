(set-logic HORN)


(declare-fun |state| ( Bool Bool Int Int Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Int Bool Bool Bool Bool Bool Bool Bool Int Int Int Bool Bool Bool Bool Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Int) (L Int) (M Bool) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) (C1 Int) (D1 Bool) (E1 Bool) (F1 Bool) (G1 Bool) (H1 Bool) (I1 Bool) ) 
    (=>
      (and
        (let ((a!1 (= (or (not B1) (not (<= 4 C1))) A1)))
  (and (= Q 0)
       (= Q D)
       (= P 0)
       (= P B)
       (= A O)
       (= D C)
       (= K 0)
       (= K A)
       (= (= A 10) I1)
       (= (<= 3 B) E1)
       (= (<= 4 D) G1)
       a!1
       (not (= (and X W) Y))
       (= V M)
       (= U H)
       (= T F)
       (= F E)
       (= I1 H1)
       (= G1 F1)
       (= E1 D1)
       (= H G)
       (= J B1)
       (= M I)
       (= Z J)
       (= Z Y)
       (or H (= S R) (not F))
       (or (= S 0) (and (not H) F))
       (not V)
       (not U)
       (= T true)
       (= B C1)))
      )
      (state Z
       Y
       Q
       P
       K
       U
       V
       T
       J
       X
       W
       M
       H
       F
       S
       R
       D
       B
       A
       I1
       G1
       E1
       B1
       I
       G
       E
       C
       C1
       O
       H1
       F1
       D1
       A1
       L
       N)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Int) (L Int) (M Bool) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Int) (B1 Bool) (C1 Bool) (D1 Int) (E1 Int) (F1 Bool) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Bool) (Q1 Bool) (R1 Bool) (S1 Bool) (T1 Int) (U1 Bool) (V1 Bool) (W1 Bool) (X1 Bool) (Y1 Bool) (Z1 Bool) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Bool) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Int) (M2 Bool) (N2 Bool) (O2 Bool) (P2 Bool) (Q2 Bool) (R2 Bool) ) 
    (=>
      (and
        (state Z
       Y
       Q
       P
       K
       U
       V
       T
       J
       X
       W
       M
       H
       F
       S
       R
       D
       B
       A
       R2
       P2
       N2
       K2
       I
       G
       E
       C
       L2
       O
       Q2
       O2
       M2
       J2
       L
       N)
        (let ((a!1 (= (or (not K2) (not (<= 4 L2))) J2))
      (a!2 (= (or (not S1) (not (<= 4 T1))) R1))
      (a!3 (or (not C1) (not B1) (= (+ B (* (- 1) A1)) (- 1))))
      (a!4 (or (not C1) (not B1) (= (+ A (* (- 1) D1)) (- 1))))
      (a!5 (or (not F1) (= (+ D (* (- 1) E1)) (- 1)))))
  (and (= N1 M1)
       (= O1 E1)
       (= B2 L1)
       (= B2 A2)
       (= C2 M1)
       (= C2 T1)
       (= E2 O1)
       (= E2 D2)
       (= Q D)
       (= P B)
       (= K A)
       (= D C)
       (= B L2)
       (= A O)
       (= (= B2 10) Z1)
       (= (= A 10) R2)
       (= (<= 3 C2) V1)
       (= (<= 3 B) N2)
       (= (<= 4 E2) X1)
       (= (<= 4 D) P2)
       a!1
       a!2
       (not (= (and H1 G1) P1))
       (not (= (and W X) Y))
       (= R2 Q2)
       (= P2 O2)
       (= N2 M2)
       (= B1 K1)
       (= B1 F2)
       (= C1 I1)
       (= C1 H2)
       (= F1 J1)
       (= F1 G2)
       (= G1 J1)
       (= I1 (and H1 (not G1)))
       (= K1 (and F (not N2) (not P2) (not R2)))
       (= Q1 (and J P1))
       (= V1 U1)
       (= X1 W1)
       (= Z1 Y1)
       (= I2 Q1)
       (= I2 S1)
       (= Z J)
       (= V M)
       (= U H)
       (= T F)
       (= M I)
       (= J K2)
       (= H G)
       (= F E)
       a!3
       a!4
       (or F1 (= N1 A1) (not B1))
       (or H (= S R) (not F))
       (or (= B A1) (and C1 B1))
       (or (and C1 B1) (= A D1))
       (or (= N1 0) (and (not F1) B1))
       (or (= S 0) (and F (not H)))
       a!5
       (or F1 (= D E1))
       (= L1 D1)))
      )
      (state Q1
       P1
       O1
       M1
       L1
       J1
       I1
       K1
       I2
       G1
       H1
       C1
       F1
       B1
       N1
       A1
       E2
       C2
       B2
       Z1
       X1
       V1
       S1
       H2
       G2
       F2
       D2
       T1
       A2
       Y1
       W1
       U1
       R1
       D1
       E1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Int) (L Int) (M Bool) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) (C1 Int) (D1 Bool) (E1 Bool) (F1 Bool) (G1 Bool) (H1 Bool) (I1 Bool) ) 
    (=>
      (and
        (state Z
       Y
       Q
       P
       K
       U
       V
       T
       J
       X
       W
       M
       H
       F
       S
       R
       D
       B
       A
       I1
       G1
       E1
       B1
       I
       G
       E
       C
       C1
       O
       H1
       F1
       D1
       A1
       L
       N)
        (not A1)
      )
      false
    )
  )
)

(check-sat)
(exit)
