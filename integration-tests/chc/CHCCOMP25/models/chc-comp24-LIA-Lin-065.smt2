(set-logic HORN)


(declare-fun |state| ( Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Int Int Int Int Int Int Bool Int Int Int Int Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool Bool Int Int Int Bool Bool Bool Bool Bool ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Bool) (F Int) (G Bool) (H Int) (I Bool) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Bool) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Bool) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Bool) (I1 Int) (J1 Int) (K1 Int) (L1 Bool) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Bool) (R1 Int) (S1 Int) (T1 Int) (U1 Bool) (V1 Bool) (W1 Int) (X1 Int) (Y1 Bool) (Z1 Int) (A2 Bool) (B2 Int) (C2 Bool) (D2 Int) (E2 Bool) (F2 Int) (G2 Bool) (H2 Bool) (I2 Int) (J2 Int) (K2 Int) (L2 Bool) (M2 Int) (N2 Int) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Bool) (V2 Int) (W2 Int) (X2 Int) ) 
    (=>
      (and
        (let ((a!1 (= R (and Q (<= 0 J) (not (<= 5 J)))))
      (a!2 (= (or (and (not Q1)
                       (not H1)
                       (not D)
                       (not U2)
                       (not V)
                       (not B1)
                       (not L1)
                       (not H2))
                  (and (not Q1)
                       (not H1)
                       (not D)
                       (not U2)
                       (not V)
                       (not B1)
                       (not L1)
                       H2)
                  (and (not Q1)
                       (not H1)
                       (not D)
                       (not U2)
                       (not V)
                       (not B1)
                       L1
                       (not H2))
                  (and (not Q1)
                       (not H1)
                       (not D)
                       (not U2)
                       (not V)
                       B1
                       (not L1)
                       (not H2))
                  (and (not Q1)
                       (not H1)
                       (not D)
                       (not U2)
                       V
                       (not B1)
                       (not L1)
                       (not H2))
                  (and (not Q1)
                       (not H1)
                       (not D)
                       U2
                       (not V)
                       (not B1)
                       (not L1)
                       (not H2))
                  (and (not Q1)
                       (not H1)
                       D
                       (not U2)
                       (not V)
                       (not B1)
                       (not L1)
                       (not H2))
                  (and (not Q1)
                       H1
                       (not D)
                       (not U2)
                       (not V)
                       (not B1)
                       (not L1)
                       (not H2))
                  (and Q1
                       (not H1)
                       (not D)
                       (not U2)
                       (not V)
                       (not B1)
                       (not L1)
                       (not H2)))
              Q)))
  (and (= (or (not V1) (<= 0 Z1)) U1)
       (= L2 V1)
       a!1
       (= R L2)
       (= K2 J2)
       (= B2 Z1)
       (= W1 D2)
       (= L B2)
       (= K J)
       (= K M)
       (= M L)
       (= N 0)
       (= N W1)
       (= O 0)
       (= O I2)
       (= P 0)
       (= P K2)
       (= I2 X1)
       (or (not H2) (= R2 Q2))
       (or (= O2 R2) H2)
       (or (= N2 M2) H2)
       (or (not H2) (= M2 P2))
       (or (not H2) (= S F2))
       (or (= T S) H2)
       (or (= K1 T2) L1)
       (or (not L1) (= K1 M1))
       (or (not L1) (= F1 N1))
       (or (= O1 F1) L1)
       (or (not B1) (= N2 E1))
       (or (not B1) (= T C1))
       (or (not B1) (= Z F))
       (or (= A1 T) B1)
       (or (= D1 Z) B1)
       (or B1 (= F1 N2))
       (or (= U S) V)
       (or (not V) (= U W))
       (or (not V) (= Y X))
       (or (= Z Y) V)
       (or (not G) (= H 1))
       (or (not E) (= F 0))
       (or (not U2) (= W2 V2))
       (or (not U2) (= T2 S2))
       (or (not U2) (= A X2))
       (or (not D) (= C B))
       (or D (= O1 A))
       (or (not D) (= O1 T1))
       (or D (= P1 W2))
       (or (not D) (= P1 S1))
       (or (not I) (= S2 0))
       (or H1 (= K1 D1))
       (or H1 (= G1 O2))
       (or (not H1) (= O2 I1))
       (or (not H1) (= D1 J1))
       (or (not Q1) (= G1 H))
       (or Q1 (= G1 C))
       (or (not Q1) (= A1 R1))
       (or Q1 (= P1 A1))
       a!2))
      )
      (state R
       L2
       V
       H2
       B1
       H1
       L1
       Q1
       D
       U2
       Q
       K
       M
       P
       K2
       O
       I2
       N
       W1
       L
       B2
       V1
       J2
       X1
       D2
       Z1
       U1
       O1
       A
       T1
       P1
       S1
       W2
       G1
       C
       H
       A1
       R1
       F1
       N1
       K1
       M1
       T2
       D1
       J1
       O2
       I1
       N2
       E1
       Z
       F
       T
       C1
       Y
       X
       U
       W
       S
       M2
       P2
       R2
       Q2
       F2
       J
       S2
       I
       G
       E
       B
       X2
       V2
       Y1
       A2
       C2
       E2
       G2)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Bool) (F Int) (G Bool) (H Int) (I Bool) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Bool) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Bool) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Bool) (I1 Int) (J1 Int) (K1 Int) (L1 Bool) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Bool) (R1 Int) (S1 Int) (T1 Int) (U1 Bool) (V1 Bool) (W1 Int) (X1 Int) (Y1 Bool) (Z1 Int) (A2 Bool) (B2 Int) (C2 Bool) (D2 Int) (E2 Bool) (F2 Int) (G2 Bool) (H2 Bool) (I2 Int) (J2 Int) (K2 Int) (L2 Bool) (M2 Int) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Bool) (V2 Int) (W2 Int) (X2 Bool) (Y2 Int) (Z2 Bool) (A3 Int) (B3 Bool) (C3 Int) (D3 Bool) (E3 Int) (F3 Bool) (G3 Bool) (H3 Int) (I3 Int) (J3 Bool) (K3 Int) (L3 Int) (M3 Int) (N3 Int) (O3 Int) (P3 Bool) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Int) (D4 Int) (E4 Bool) (F4 Bool) (G4 Int) (H4 Int) (I4 Bool) (J4 Int) (K4 Int) (L4 Bool) (M4 Int) (N4 Int) (O4 Bool) (P4 Int) (Q4 Int) (R4 Int) (S4 Bool) (T4 Int) (U4 Bool) (V4 Int) (W4 Int) (X4 Bool) (Y4 Bool) (Z4 Bool) (A5 Int) (B5 Int) (C5 Int) (D5 Int) (E5 Int) (F5 Int) (G5 Int) (H5 Int) (I5 Bool) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Bool) (T5 Int) (U5 Int) (V5 Int) ) 
    (=>
      (and
        (state R
       L2
       V
       H2
       B1
       H1
       L1
       Q1
       D
       S5
       Q
       K
       M
       P
       K2
       O
       I2
       N
       W1
       L
       B2
       V1
       J2
       X1
       D2
       Z1
       U1
       O1
       A
       T1
       P1
       S1
       U5
       G1
       C
       H
       A1
       R1
       F1
       N1
       K1
       M1
       R5
       D1
       J1
       M5
       I1
       L5
       E1
       Z
       F
       T
       C1
       Y
       X
       U
       W
       S
       K5
       N5
       P5
       O5
       F2
       J
       Q5
       I
       G
       E
       B
       V5
       T5
       Y1
       A2
       C2
       E2
       G2)
        (let ((a!1 (= (or (and (not X4)
                       (not U4)
                       (not S4)
                       (not O4)
                       (not L4)
                       (not I4)
                       (not U2)
                       (not N2))
                  (and (not X4)
                       (not U4)
                       (not S4)
                       (not O4)
                       (not L4)
                       (not I4)
                       (not U2)
                       N2)
                  (and (not X4)
                       (not U4)
                       (not S4)
                       (not O4)
                       (not L4)
                       (not I4)
                       U2
                       (not N2))
                  (and (not X4)
                       (not U4)
                       (not S4)
                       (not O4)
                       (not L4)
                       I4
                       (not U2)
                       (not N2))
                  (and (not X4)
                       (not U4)
                       (not S4)
                       (not O4)
                       L4
                       (not I4)
                       (not U2)
                       (not N2))
                  (and (not X4)
                       (not U4)
                       (not S4)
                       O4
                       (not L4)
                       (not I4)
                       (not U2)
                       (not N2))
                  (and (not X4)
                       (not U4)
                       S4
                       (not O4)
                       (not L4)
                       (not I4)
                       (not U2)
                       (not N2))
                  (and (not X4)
                       U4
                       (not S4)
                       (not O4)
                       (not L4)
                       (not I4)
                       (not U2)
                       (not N2))
                  (and X4
                       (not U4)
                       (not S4)
                       (not O4)
                       (not L4)
                       (not I4)
                       (not U2)
                       (not N2)))
              E4))
      (a!2 (= (or (and (not D)
                       (not V)
                       (not B1)
                       (not H1)
                       (not L1)
                       (not Q1)
                       (not H2)
                       (not S5))
                  (and (not D)
                       (not V)
                       (not B1)
                       (not H1)
                       (not L1)
                       (not Q1)
                       (not H2)
                       S5)
                  (and (not D)
                       (not V)
                       (not B1)
                       (not H1)
                       (not L1)
                       (not Q1)
                       H2
                       (not S5))
                  (and (not D)
                       (not V)
                       (not B1)
                       (not H1)
                       (not L1)
                       Q1
                       (not H2)
                       (not S5))
                  (and (not D)
                       (not V)
                       (not B1)
                       (not H1)
                       L1
                       (not Q1)
                       (not H2)
                       (not S5))
                  (and (not D)
                       (not V)
                       (not B1)
                       H1
                       (not L1)
                       (not Q1)
                       (not H2)
                       (not S5))
                  (and (not D)
                       (not V)
                       B1
                       (not H1)
                       (not L1)
                       (not Q1)
                       (not H2)
                       (not S5))
                  (and (not D)
                       V
                       (not B1)
                       (not H1)
                       (not L1)
                       (not Q1)
                       (not H2)
                       (not S5))
                  (and D
                       (not V)
                       (not B1)
                       (not H1)
                       (not L1)
                       (not Q1)
                       (not H2)
                       (not S5)))
              Q))
      (a!3 (and (<= 1 B2) (= W1 0) (= I2 0) (= K2 0)))
      (a!4 (= (and (<= 1 B2) (<= 1 (+ K2 I2))) B3))
      (a!5 (= G3 (and (<= 1 B2) (<= 1 (+ K2 I2)))))
      (a!6 (or L2 (and E4 (<= 0 D4) (not (<= 5 D4)))))
      (a!7 (or (not X2) (= (+ I2 (* (- 1) L3)) (- 1))))
      (a!8 (or (not X2) (= (+ B2 (* (- 1) W2)) 1)))
      (a!9 (or (not Z2) (= (+ K2 (* (- 1) R3)) (- 2))))
      (a!10 (or (not Z2) (= (+ B2 (* (- 1) Y2)) 1)))
      (a!11 (or (not Z2) (= (+ W1 (* (- 1) H3)) 1)))
      (a!12 (or (not B3) (= (+ K2 I2 (* (- 1) Q3)) 0)))
      (a!13 (or (not B3) (= (+ B2 (* (- 1) A3)) 1)))
      (a!14 (or (not D3) (= (+ B2 (* (- 1) C3)) 1)))
      (a!15 (or (not F3) (= (+ K2 (* (- 1) T3)) (- 2))))
      (a!16 (or (not F3) (= (+ B2 (* (- 1) E3)) 1)))
      (a!17 (or (not F3) (= (+ W1 (* (- 1) V2)) 1)))
      (a!18 (or (not G3) (= (+ K2 I2 (* (- 1) R2)) (- 1))))
      (a!19 (or (not G3) (= (+ B2 (* (- 1) O2)) 1)))
      (a!20 (or (not J3) (= (+ I2 (* (- 1) N3)) 1)))
      (a!21 (or (not J3) (= (+ W1 (* (- 1) I3)) (- 1))))
      (a!22 (or (not P3) (= (+ I2 (* (- 1) O3)) (- 1)))))
  (and a!1
       a!2
       (= (or (not Z4) (<= 0 A5)) Y4)
       (= (or (not V1) (<= 0 Z1)) U1)
       (= a!3 X2)
       a!4
       (= (and (<= 1 W1) (<= 1 B2)) Z2)
       (= (and (<= 1 W1) (<= 1 B2)) F3)
       (= D3 a!3)
       a!5
       (= P3 (= K2 1))
       (= F4 a!6)
       (= I5 F4)
       (= I5 Z4)
       (= L2 V1)
       (= R L2)
       (= W3 V3)
       (= Y3 X3)
       (= A4 Z3)
       (= C4 B4)
       (= B5 W3)
       (= B5 A5)
       (= D5 Y3)
       (= D5 C5)
       (= F5 A4)
       (= F5 E5)
       (= H5 C4)
       (= H5 G5)
       (= J5 U3)
       (= K2 J2)
       (= I2 X1)
       (= B2 Z1)
       (= W1 D2)
       (= P K2)
       (= O I2)
       (= N W1)
       (= M U3)
       (= L B2)
       (= K M)
       (or (not N2) (= M2 O2))
       (or (not N2) (= Q2 P2))
       (or (not N2) (= S2 R2))
       (or N2 (= K2 S2))
       (or N2 (= I2 Q2))
       (or N2 (= B2 M2))
       (or U2 (= S2 V4))
       (or (not U2) (= T2 V2))
       (or (not U2) (= E3 W4))
       (or (not U2) (= V4 T3))
       (or U2 (= W4 M2))
       (or U2 (= W1 T2))
       a!7
       a!8
       (or X2 (= I2 L3))
       (or X2 (= B2 W2))
       a!9
       a!10
       a!11
       (or Z2 (= K2 R3))
       (or Z2 (= B2 Y2))
       (or Z2 (= W1 H3))
       a!12
       a!13
       (or (not B3) (= M3 0))
       (or B3 (= K2 Q3))
       (or B3 (= I2 M3))
       (or B3 (= B2 A3))
       a!14
       (or (not D3) (= K3 1))
       (or D3 (= B2 C3))
       (or D3 (= W1 K3))
       a!15
       a!16
       a!17
       (or F3 (= K2 T3))
       (or F3 (= B2 E3))
       (or F3 (= W1 V2))
       a!18
       a!19
       (or (not G3) (= P2 0))
       (or G3 (= K2 R2))
       (or G3 (= I2 P2))
       (or G3 (= B2 O2))
       a!20
       a!21
       (or J3 (= I2 N3))
       (or J3 (= W1 I3))
       a!22
       (or (not P3) (= S3 0))
       (or P3 (= K2 S3))
       (or P3 (= I2 O3))
       (or (not I4) (= X3 H3))
       (or (not I4) (= B4 R3))
       (or (not I4) (= G4 Y2))
       (or I4 (= H4 G4))
       (or I4 (= J4 X3))
       (or I4 (= K4 B4))
       (or (not L4) (= W2 V3))
       (or L4 (= V3 G4))
       (or (not L4) (= Z3 L3))
       (or L4 (= M4 Z3))
       (or (not O4) (= A3 H4))
       (or (not O4) (= K4 Q3))
       (or (not O4) (= M4 M3))
       (or O4 (= N4 H4))
       (or O4 (= P4 M4))
       (or O4 (= Q4 K4))
       (or (not S4) (= I3 J4))
       (or (not S4) (= P4 N3))
       (or S4 (= R4 J4))
       (or S4 (= T4 P4))
       (or (not U4) (= O3 T4))
       (or (not U4) (= Q4 S3))
       (or U4 (= T4 Q2))
       (or U4 (= V4 Q4))
       (or X4 (= T2 R4))
       (or (not X4) (= C3 N4))
       (or (not X4) (= R4 K3))
       (or X4 (= W4 N4))
       (or (not H2) (= P5 O5))
       (or H2 (= M5 P5))
       (or H2 (= L5 K5))
       (or (not H2) (= K5 N5))
       (or H2 (= T S))
       (or (not H2) (= S F2))
       (or Q1 (= P1 A1))
       (or (not Q1) (= G1 H))
       (or Q1 (= G1 C))
       (or (not Q1) (= A1 R1))
       (or L1 (= O1 F1))
       (or L1 (= K1 R5))
       (or (not L1) (= K1 M1))
       (or (not L1) (= F1 N1))
       (or (not H1) (= M5 I1))
       (or H1 (= K1 D1))
       (or H1 (= G1 M5))
       (or (not H1) (= D1 J1))
       (or (not B1) (= L5 E1))
       (or B1 (= F1 L5))
       (or B1 (= D1 Z))
       (or B1 (= A1 T))
       (or (not B1) (= Z F))
       (or (not B1) (= T C1))
       (or V (= Z Y))
       (or (not V) (= Y X))
       (or (not V) (= U W))
       (or V (= U S))
       (or D (= P1 U5))
       (or (not D) (= P1 S1))
       (or (not D) (= O1 T1))
       (or D (= O1 A))
       (= (<= 1 I2) J3)))
      )
      (state F4
       I5
       L4
       I4
       O4
       S4
       U4
       X4
       U2
       N2
       E4
       U3
       J5
       C4
       H5
       A4
       F5
       Y3
       D5
       W3
       B5
       Z4
       G5
       E5
       C5
       A5
       Y4
       V4
       S2
       T3
       W4
       E3
       M2
       R4
       T2
       K3
       N4
       C3
       Q4
       S3
       T4
       O3
       Q2
       P4
       N3
       J4
       I3
       K4
       Q3
       M4
       M3
       H4
       A3
       Z3
       L3
       V3
       W2
       G4
       B4
       R3
       X3
       H3
       Y2
       D4
       P2
       G3
       D3
       B3
       V2
       R2
       O2
       X2
       Z2
       J3
       P3
       F3)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Bool) (F Int) (G Bool) (H Int) (I Bool) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Bool) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Bool) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Bool) (I1 Int) (J1 Int) (K1 Int) (L1 Bool) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Bool) (R1 Int) (S1 Int) (T1 Int) (U1 Bool) (V1 Bool) (W1 Int) (X1 Int) (Y1 Bool) (Z1 Int) (A2 Bool) (B2 Int) (C2 Bool) (D2 Int) (E2 Bool) (F2 Int) (G2 Bool) (H2 Bool) (I2 Int) (J2 Int) (K2 Int) (L2 Bool) (M2 Int) (N2 Int) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Bool) (V2 Int) (W2 Int) (X2 Int) ) 
    (=>
      (and
        (state R
       L2
       V
       H2
       B1
       H1
       L1
       Q1
       D
       U2
       Q
       K
       M
       P
       K2
       O
       I2
       N
       W1
       L
       B2
       V1
       J2
       X1
       D2
       Z1
       U1
       O1
       A
       T1
       P1
       S1
       W2
       G1
       C
       H
       A1
       R1
       F1
       N1
       K1
       M1
       T2
       D1
       J1
       O2
       I1
       N2
       E1
       Z
       F
       T
       C1
       Y
       X
       U
       W
       S
       M2
       P2
       R2
       Q2
       F2
       J
       S2
       I
       G
       E
       B
       X2
       V2
       Y1
       A2
       C2
       E2
       G2)
        (not U1)
      )
      false
    )
  )
)

(check-sat)
(exit)
