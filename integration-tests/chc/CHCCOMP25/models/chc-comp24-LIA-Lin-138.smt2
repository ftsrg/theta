(set-logic HORN)


(declare-fun |f_1034$unknown:58| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |fail$unknown:96| ( Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) ) 
    (=>
      (and
        (|f_1034$unknown:58| W V U T S R Q P O N M L K J I H G F E D C B A)
        (and (= X 1) (not (= 0 S)))
      )
      (|fail$unknown:96| X)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Int) (H2 Int) (I2 Int) (J2 Int) (K2 Int) (L2 Int) (M2 Int) (N2 Int) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) ) 
    (=>
      (and
        (and (= A 0)
     (= H 0)
     (= G 0)
     (= F 0)
     (= E 0)
     (= D 0)
     (= C 0)
     (= X 0)
     (= W 0)
     (= V 0)
     (= U 0)
     (= T 0)
     (= S 0)
     (= R 0)
     (= Q 0)
     (= P 0)
     (= O 0)
     (= N 0)
     (= M 0)
     (= L 0)
     (= K 0)
     (= J 0)
     (= I 0)
     (= I2 0)
     (= H2 0)
     (= G2 0)
     (= F2 0)
     (= E2 0)
     (= D2 0)
     (= C2 0)
     (= B2 0)
     (= A2 0)
     (= Z1 0)
     (= Y1 0)
     (= X1 0)
     (= W1 0)
     (= V1 0)
     (= U1 0)
     (= T1 0)
     (= S1 0)
     (= R1 0)
     (= Q1 0)
     (= P1 0)
     (= O1 0)
     (= N1 0)
     (= M1 0)
     (= L1 0)
     (= K1 0)
     (= J1 0)
     (= I1 0)
     (= H1 0)
     (= G1 0)
     (= F1 0)
     (= E1 0)
     (= D1 0)
     (= C1 0)
     (= B1 0)
     (= A1 0)
     (= Z 0)
     (= Y 0)
     (= Y2 0)
     (= X2 0)
     (= W2 0)
     (= V2 0)
     (= U2 0)
     (= T2 0)
     (= S2 1)
     (= R2 0)
     (= Q2 0)
     (= P2 0)
     (= O2 0)
     (= N2 0)
     (= M2 0)
     (= L2 0)
     (= K2 0)
     (= J2 0)
     (= B 0))
      )
      (|f_1034$unknown:58|
  S2
  R2
  Q2
  P2
  O2
  N2
  M2
  L2
  K2
  A
  J2
  I2
  H2
  G2
  F2
  E2
  D2
  C2
  C
  B2
  A2
  Z1
  Y1)
    )
  )
)
(assert
  (forall ( (A Int) ) 
    (=>
      (and
        (|fail$unknown:96| A)
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
