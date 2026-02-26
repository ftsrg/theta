(set-logic HORN)


(declare-fun |state| ( Int Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool Bool Int Int Int Bool Bool Bool Bool Bool ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Bool) (F Int) (G Bool) (H Int) (I Bool) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) (R Bool) (S Bool) (T Int) (U Int) (V Int) (W Int) (X Bool) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Bool) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Bool) (N1 Int) (O1 Int) (P1 Int) (Q1 Bool) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Bool) (W1 Int) (X1 Int) (Y1 Bool) (Z1 Int) (A2 Bool) (B2 Int) (C2 Bool) (D2 Bool) (E2 Bool) (F2 Int) (G2 Bool) (H2 Int) (I2 Bool) (J2 Int) (K2 Int) (L2 Int) (M2 Int) (N2 Int) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Bool) (T2 Int) (U2 Int) (V2 Int) (W2 Bool) (X2 Int) (Y2 Int) (Z2 Int) ) 
    (=>
      (and
        (let ((a!1 (or (not R)
               (= (+ L2 (* (- 1) K2) (* (- 1) Z1) (* (- 1) O2) (* (- 1) Q2)) 0)))
      (a!2 (= (or (and (not D2)
                       (not Q1)
                       (not G1)
                       (not D)
                       (not W2)
                       (not X)
                       (not M1)
                       (not V1))
                  (and (not D2)
                       (not Q1)
                       (not G1)
                       (not D)
                       (not W2)
                       (not X)
                       (not M1)
                       V1)
                  (and (not D2)
                       (not Q1)
                       (not G1)
                       (not D)
                       (not W2)
                       (not X)
                       M1
                       (not V1))
                  (and (not D2)
                       (not Q1)
                       (not G1)
                       (not D)
                       (not W2)
                       X
                       (not M1)
                       (not V1))
                  (and (not D2)
                       (not Q1)
                       (not G1)
                       (not D)
                       W2
                       (not X)
                       (not M1)
                       (not V1))
                  (and (not D2)
                       (not Q1)
                       (not G1)
                       D
                       (not W2)
                       (not X)
                       (not M1)
                       (not V1))
                  (and (not D2)
                       (not Q1)
                       G1
                       (not D)
                       (not W2)
                       (not X)
                       (not M1)
                       (not V1))
                  (and (not D2)
                       Q1
                       (not G1)
                       (not D)
                       (not W2)
                       (not X)
                       (not M1)
                       (not V1))
                  (and D2
                       (not Q1)
                       (not G1)
                       (not D)
                       (not W2)
                       (not X)
                       (not M1)
                       (not V1)))
              Q)))
  (and (= a!1 Y1)
       (= S R)
       (= S2 (and Q (<= 0 J)))
       (= S2 S)
       (= L M2)
       (= T2 J)
       (= T2 L2)
       (= R2 Q2)
       (= P2 O2)
       (= K J)
       (= K M)
       (= M L)
       (= N 0)
       (= N N2)
       (= O 0)
       (= O R2)
       (= P 0)
       (= P P2)
       (= M2 Z1)
       (= N2 K2)
       (or (not V1) (= F1 W1))
       (or (not V1) (= L1 H))
       (or (= L1 C) V1)
       (or (= U1 F1) V1)
       (or (not M1) (= B1 N1))
       (or (not M1) (= I1 O1))
       (or (= L1 B1) M1)
       (or (= P1 I1) M1)
       (or (= W J2) X)
       (or (not X) (= A1 Z))
       (or (= B1 A1) X)
       (or (not X) (= D1 C1))
       (or (= E1 D1) X)
       (or (not X) (= J2 Y))
       (or (not G) (= H 1))
       (or (not E) (= F 0))
       (or (not W2) (= Y2 X2))
       (or (not W2) (= V2 U2))
       (or (not W2) (= A Z2))
       (or (not D) (= T1 B2))
       (or D (= T1 A))
       (or (not D) (= C B))
       (or (not D) (= U1 X1))
       (or D (= U1 Y2))
       (or (not I) (= U2 0))
       (or (not G1) (= V F))
       (or (not G1) (= W H1))
       (or (not G1) (= E1 J1))
       (or G1 (= F1 W))
       (or G1 (= I1 V))
       (or G1 (= K1 E1))
       (or Q1 (= T1 K1))
       (or (not Q1) (= K1 S1))
       (or Q1 (= P1 V2))
       (or (not Q1) (= P1 R1))
       (or (not D2) (= T F2))
       (or (not D2) (= U H2))
       (or D2 (= V U))
       (or D2 (= J2 T))
       a!2))
      )
      (state T2
       L2
       S2
       S
       X
       D2
       G1
       M1
       Q1
       V1
       D
       W2
       Q
       K
       M
       P
       P2
       O
       R2
       N
       N2
       L
       M2
       K2
       Z1
       O2
       Q2
       R
       Y1
       T1
       A
       B2
       U1
       X1
       Y2
       L1
       C
       H
       F1
       W1
       K1
       S1
       P1
       R1
       V2
       I1
       O1
       B1
       N1
       E1
       J1
       V
       F
       W
       H1
       D1
       C1
       A1
       Z
       J2
       Y
       U
       H2
       T
       F2
       J
       U2
       I
       G
       E
       B
       Z2
       X2
       A2
       C2
       E2
       G2
       I2)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Bool) (F Int) (G Bool) (H Int) (I Bool) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) (R Bool) (S Bool) (T Int) (U Int) (V Int) (W Int) (X Bool) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Bool) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Bool) (N1 Int) (O1 Int) (P1 Int) (Q1 Bool) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Bool) (W1 Int) (X1 Int) (Y1 Bool) (Z1 Int) (A2 Bool) (B2 Int) (C2 Bool) (D2 Bool) (E2 Bool) (F2 Int) (G2 Bool) (H2 Int) (I2 Bool) (J2 Int) (K2 Int) (L2 Int) (M2 Int) (N2 Int) (O2 Int) (P2 Bool) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Bool) (X2 Int) (Y2 Int) (Z2 Bool) (A3 Int) (B3 Bool) (C3 Int) (D3 Bool) (E3 Int) (F3 Bool) (G3 Int) (H3 Bool) (I3 Bool) (J3 Int) (K3 Int) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Bool) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Int) (D4 Int) (E4 Int) (F4 Int) (G4 Bool) (H4 Bool) (I4 Int) (J4 Int) (K4 Int) (L4 Int) (M4 Int) (N4 Bool) (O4 Bool) (P4 Int) (Q4 Bool) (R4 Int) (S4 Int) (T4 Bool) (U4 Int) (V4 Int) (W4 Int) (X4 Bool) (Y4 Int) (Z4 Int) (A5 Int) (B5 Bool) (C5 Int) (D5 Bool) (E5 Int) (F5 Int) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Bool) (T5 Int) (U5 Int) (V5 Int) (W5 Bool) (X5 Int) (Y5 Int) (Z5 Int) ) 
    (=>
      (and
        (state T5
       L2
       S5
       S
       X
       D2
       G1
       M1
       Q1
       V1
       D
       W5
       Q
       K
       M
       P
       P5
       O
       R5
       N
       N2
       L
       M2
       K2
       Z1
       O5
       Q5
       R
       Y1
       T1
       A
       B2
       U1
       X1
       Y5
       L1
       C
       H
       F1
       W1
       K1
       S1
       P1
       R1
       V5
       I1
       O1
       B1
       N1
       E1
       J1
       V
       F
       W
       H1
       D1
       C1
       A1
       Z
       J2
       Y
       U
       H2
       T
       F2
       J
       U5
       I
       G
       E
       B
       Z5
       X5
       A2
       C2
       E2
       G2
       I2)
        (let ((a!1 (= (or (and (not G5)
                       (not D5)
                       (not B5)
                       (not X4)
                       (not T4)
                       (not Q4)
                       (not W2)
                       (not P2))
                  (and (not G5)
                       (not D5)
                       (not B5)
                       (not X4)
                       (not T4)
                       (not Q4)
                       (not W2)
                       P2)
                  (and (not G5)
                       (not D5)
                       (not B5)
                       (not X4)
                       (not T4)
                       (not Q4)
                       W2
                       (not P2))
                  (and (not G5)
                       (not D5)
                       (not B5)
                       (not X4)
                       (not T4)
                       Q4
                       (not W2)
                       (not P2))
                  (and (not G5)
                       (not D5)
                       (not B5)
                       (not X4)
                       T4
                       (not Q4)
                       (not W2)
                       (not P2))
                  (and (not G5)
                       (not D5)
                       (not B5)
                       X4
                       (not T4)
                       (not Q4)
                       (not W2)
                       (not P2))
                  (and (not G5)
                       (not D5)
                       B5
                       (not X4)
                       (not T4)
                       (not Q4)
                       (not W2)
                       (not P2))
                  (and (not G5)
                       D5
                       (not B5)
                       (not X4)
                       (not T4)
                       (not Q4)
                       (not W2)
                       (not P2))
                  (and G5
                       (not D5)
                       (not B5)
                       (not X4)
                       (not T4)
                       (not Q4)
                       (not W2)
                       (not P2)))
              G4))
      (a!2 (= (or (and (not D)
                       (not X)
                       (not G1)
                       (not M1)
                       (not Q1)
                       (not V1)
                       (not D2)
                       (not W5))
                  (and (not D)
                       (not X)
                       (not G1)
                       (not M1)
                       (not Q1)
                       (not V1)
                       (not D2)
                       W5)
                  (and (not D)
                       (not X)
                       (not G1)
                       (not M1)
                       (not Q1)
                       (not V1)
                       D2
                       (not W5))
                  (and (not D)
                       (not X)
                       (not G1)
                       (not M1)
                       (not Q1)
                       V1
                       (not D2)
                       (not W5))
                  (and (not D)
                       (not X)
                       (not G1)
                       (not M1)
                       Q1
                       (not V1)
                       (not D2)
                       (not W5))
                  (and (not D)
                       (not X)
                       (not G1)
                       M1
                       (not Q1)
                       (not V1)
                       (not D2)
                       (not W5))
                  (and (not D)
                       (not X)
                       G1
                       (not M1)
                       (not Q1)
                       (not V1)
                       (not D2)
                       (not W5))
                  (and (not D)
                       X
                       (not G1)
                       (not M1)
                       (not Q1)
                       (not V1)
                       (not D2)
                       (not W5))
                  (and D
                       (not X)
                       (not G1)
                       (not M1)
                       (not Q1)
                       (not V1)
                       (not D2)
                       (not W5)))
              Q))
      (a!3 (or (not N4)
               (= (+ K5 (* (- 1) J5) (* (- 1) I5) (* (- 1) L4) (* (- 1) J4)) 0)))
      (a!4 (or (not R)
               (= (+ L2 (* (- 1) K2) (* (- 1) Z1) (* (- 1) O5) (* (- 1) Q5)) 0)))
      (a!5 (and (<= 1 M2) (= N2 0) (= P5 0) (= R5 0)))
      (a!6 (= (and (<= 1 M2) (<= 1 (+ P5 R5))) D3))
      (a!7 (= I3 (and (<= 1 M2) (<= 1 (+ P5 R5)))))
      (a!8 (or (not Z2) (= (+ R5 (* (- 1) N3)) (- 1))))
      (a!9 (or (not Z2) (= (+ M2 (* (- 1) Y2)) 1)))
      (a!10 (or (not B3) (= (+ P5 (* (- 1) T3)) (- 2))))
      (a!11 (or (not B3) (= (+ N2 (* (- 1) J3)) 1)))
      (a!12 (or (not B3) (= (+ M2 (* (- 1) A3)) 1)))
      (a!13 (or (not D3) (= (+ P5 (* (- 1) R5) (* (- 1) S3)) 1)))
      (a!14 (or (not D3) (= (+ M2 (* (- 1) C3)) 1)))
      (a!15 (or (not F3) (= (+ M2 (* (- 1) E3)) 1)))
      (a!16 (or (not H3) (= (+ P5 (* (- 1) V3)) (- 2))))
      (a!17 (or (not H3) (= (+ N2 (* (- 1) X2)) 1)))
      (a!18 (or (not H3) (= (+ M2 (* (- 1) G3)) 1)))
      (a!19 (or (not I3) (= (+ P5 R5 (* (- 1) T2)) (- 1))))
      (a!20 (or (not I3) (= (+ M2 (* (- 1) Q2)) 1)))
      (a!21 (or (not L3) (= (+ R5 (* (- 1) P3)) 1)))
      (a!22 (or (not L3) (= (+ N2 (* (- 1) K3)) (- 1))))
      (a!23 (or (not R3) (= (+ R5 (* (- 1) Q3)) (- 1)))))
  (and a!1
       a!2
       (= a!3 H5)
       (= a!4 Y1)
       (= a!5 Z2)
       a!6
       (= (and (<= 1 M2) (<= 1 N2)) B3)
       (= (and (<= 1 M2) (<= 1 N2)) H3)
       (= S5 S)
       (= F3 a!5)
       a!7
       (= R3 (= P5 1))
       (= H4 (and S G4 (<= 0 F4)))
       (= O4 H4)
       (= O4 N4)
       (= S R)
       (= T5 L2)
       (= R5 Q5)
       (= P5 O5)
       (= Y3 X3)
       (= A4 Z3)
       (= C4 B4)
       (= E4 D4)
       (= K4 C4)
       (= K4 J4)
       (= M4 E4)
       (= M4 L4)
       (= K5 I4)
       (= L5 Y3)
       (= L5 I5)
       (= M5 A4)
       (= M5 J5)
       (= N5 W3)
       (= N2 K2)
       (= M2 Z1)
       (= L2 I4)
       (= P P5)
       (= O R5)
       (= N N2)
       (= M W3)
       (= L M2)
       (= K M)
       (or P2 (= R5 S2))
       (or P2 (= P5 U2))
       (or (not P2) (= O2 Q2))
       (or (not P2) (= S2 R2))
       (or (not P2) (= U2 T2))
       (or P2 (= M2 O2))
       (or W2 (= U2 E5))
       (or (not W2) (= V2 X2))
       (or (not W2) (= G3 F5))
       (or (not W2) (= E5 V3))
       (or W2 (= F5 O2))
       (or W2 (= N2 V2))
       a!8
       a!9
       (or Z2 (= R5 N3))
       (or Z2 (= M2 Y2))
       a!10
       a!11
       a!12
       (or B3 (= P5 T3))
       (or B3 (= N2 J3))
       (or B3 (= M2 A3))
       a!13
       a!14
       (or D3 (= R5 O3))
       (or D3 (= P5 S3))
       (or (not D3) (= O3 0))
       (or D3 (= M2 C3))
       a!15
       (or (not F3) (= M3 1))
       (or F3 (= N2 M3))
       (or F3 (= M2 E3))
       a!16
       a!17
       a!18
       (or H3 (= P5 V3))
       (or H3 (= N2 X2))
       (or H3 (= M2 G3))
       a!19
       a!20
       (or I3 (= R5 R2))
       (or I3 (= P5 T2))
       (or (not I3) (= R2 0))
       (or I3 (= M2 Q2))
       a!21
       a!22
       (or L3 (= R5 P3))
       (or L3 (= N2 K3))
       a!23
       (or R3 (= R5 Q3))
       (or R3 (= P5 U3))
       (or (not R3) (= U3 0))
       (or (not Q4) (= Y2 X3))
       (or (not Q4) (= B4 N3))
       (or Q4 (= P4 X3))
       (or Q4 (= R4 B4))
       (or (not T4) (= A3 P4))
       (or (not T4) (= Z3 J3))
       (or (not T4) (= D4 T3))
       (or T4 (= S4 P4))
       (or T4 (= U4 Z3))
       (or T4 (= V4 D4))
       (or (not X4) (= C3 S4))
       (or (not X4) (= R4 O3))
       (or (not X4) (= V4 S3))
       (or X4 (= W4 S4))
       (or X4 (= Y4 R4))
       (or X4 (= Z4 V4))
       (or (not B5) (= K3 U4))
       (or (not B5) (= Y4 P3))
       (or B5 (= A5 U4))
       (or B5 (= C5 Y4))
       (or (not D5) (= Q3 C5))
       (or (not D5) (= Z4 U3))
       (or D5 (= C5 S2))
       (or D5 (= E5 Z4))
       (or G5 (= V2 A5))
       (or (not G5) (= E3 W4))
       (or (not G5) (= A5 M3))
       (or G5 (= F5 W4))
       (or D2 (= J2 T))
       (or D2 (= V U))
       (or (not D2) (= U H2))
       (or (not D2) (= T F2))
       (or V1 (= U1 F1))
       (or (not V1) (= L1 H))
       (or V1 (= L1 C))
       (or (not V1) (= F1 W1))
       (or Q1 (= T1 K1))
       (or Q1 (= P1 V5))
       (or (not Q1) (= P1 R1))
       (or (not Q1) (= K1 S1))
       (or M1 (= P1 I1))
       (or M1 (= L1 B1))
       (or (not M1) (= I1 O1))
       (or (not M1) (= B1 N1))
       (or G1 (= K1 E1))
       (or G1 (= I1 V))
       (or G1 (= F1 W))
       (or (not G1) (= E1 J1))
       (or (not G1) (= W H1))
       (or (not G1) (= V F))
       (or (not X) (= J2 Y))
       (or X (= E1 D1))
       (or (not X) (= D1 C1))
       (or X (= B1 A1))
       (or (not X) (= A1 Z))
       (or X (= W J2))
       (or D (= U1 Y5))
       (or (not D) (= U1 X1))
       (or (not D) (= T1 B2))
       (or D (= T1 A))
       (= (<= 1 R5) L3)))
      )
      (state I4
       K5
       H4
       O4
       T4
       Q4
       X4
       B5
       D5
       G5
       W2
       P2
       G4
       W3
       N5
       E4
       M4
       C4
       K4
       A4
       M5
       Y3
       L5
       J5
       I5
       L4
       J4
       N4
       H5
       E5
       U2
       V3
       F5
       G3
       O2
       A5
       V2
       M3
       W4
       E3
       Z4
       U3
       C5
       Q3
       S2
       Y4
       P3
       U4
       K3
       V4
       S3
       R4
       O3
       S4
       C3
       D4
       T3
       Z3
       J3
       P4
       A3
       B4
       N3
       X3
       Y2
       F4
       R2
       I3
       F3
       D3
       X2
       T2
       Q2
       Z2
       B3
       L3
       R3
       H3)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Bool) (F Int) (G Bool) (H Int) (I Bool) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) (R Bool) (S Bool) (T Int) (U Int) (V Int) (W Int) (X Bool) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Bool) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Bool) (N1 Int) (O1 Int) (P1 Int) (Q1 Bool) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Bool) (W1 Int) (X1 Int) (Y1 Bool) (Z1 Int) (A2 Bool) (B2 Int) (C2 Bool) (D2 Bool) (E2 Bool) (F2 Int) (G2 Bool) (H2 Int) (I2 Bool) (J2 Int) (K2 Int) (L2 Int) (M2 Int) (N2 Int) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Bool) (T2 Int) (U2 Int) (V2 Int) (W2 Bool) (X2 Int) (Y2 Int) (Z2 Int) ) 
    (=>
      (and
        (state T2
       L2
       S2
       S
       X
       D2
       G1
       M1
       Q1
       V1
       D
       W2
       Q
       K
       M
       P
       P2
       O
       R2
       N
       N2
       L
       M2
       K2
       Z1
       O2
       Q2
       R
       Y1
       T1
       A
       B2
       U1
       X1
       Y2
       L1
       C
       H
       F1
       W1
       K1
       S1
       P1
       R1
       V2
       I1
       O1
       B1
       N1
       E1
       J1
       V
       F
       W
       H1
       D1
       C1
       A1
       Z
       J2
       Y
       U
       H2
       T
       F2
       J
       U2
       I
       G
       E
       B
       Z2
       X2
       A2
       C2
       E2
       G2
       I2)
        (not Y1)
      )
      false
    )
  )
)

(check-sat)
(exit)
