(set-logic HORN)


(declare-fun |Assert #0: Main.java, line 13| ( ) Bool)
(declare-fun |<Main: void main(JayArray_java_lang_String)>_Block13_2| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |<Main: void main(JayArray_java_lang_String)>_Block13_1| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |<Main: void main(JayArray_java_lang_String)>_Block13_4| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |<Main: void main(JayArray_java_lang_String)>_Block13_6| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |<Main: void main(JayArray_java_lang_String)>_Block13| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |<Main: void main(JayArray_java_lang_String)>_Block13_3| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |<Main: void main(JayArray_java_lang_String)>_Block13_5| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |<Main: void main(JayArray_java_lang_String)>_pre| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (v_43 Int) (v_44 Int) (v_45 Int) (v_46 Int) (v_47 Int) (v_48 Int) (v_49 Int) (v_50 Int) (v_51 Int) (v_52 Int) (v_53 Int) (v_54 Int) (v_55 Int) (v_56 Int) (v_57 Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_pre|
  S
  I
  P
  G
  M
  B
  T
  F1
  B1
  Z
  R
  V
  L1
  K
  I1
  H)
        (and (= v_43 S)
     (= v_44 I)
     (= v_45 P)
     (= v_46 G)
     (= v_47 B)
     (= v_48 T)
     (= v_49 F1)
     (= v_50 B1)
     (= v_51 Z)
     (= v_52 R)
     (= v_53 V)
     (= v_54 L1)
     (= v_55 K)
     (= v_56 I1)
     (= v_57 H))
      )
      (|<Main: void main(JayArray_java_lang_String)>_Block13|
  S
  I
  P
  G
  M
  B
  T
  F1
  B1
  Z
  R
  V
  L1
  K
  I1
  H
  K1
  Y
  X
  Q
  J
  A
  W
  J1
  N1
  C1
  O
  E
  v_43
  v_44
  v_45
  v_46
  H1
  D1
  N
  E1
  F
  G1
  L
  A1
  D
  O1
  P1
  C
  M1
  Q1
  U
  v_47
  v_48
  v_49
  v_50
  v_51
  v_52
  v_53
  v_54
  v_55
  v_56
  v_57)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (v_55 Int) (v_56 Int) (v_57 Int) (v_58 Int) (v_59 Int) (v_60 Int) (v_61 Int) (v_62 Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_Block13|
  T
  B1
  Q
  F1
  M1
  H
  P1
  E1
  D1
  C1
  G
  K
  X
  Z1
  A1
  J1
  C2
  B2
  Y
  E
  W
  U
  P
  Q1
  I1
  F
  L
  O1
  v_55
  v_56
  v_57
  v_58
  R
  H1
  V
  X1
  B
  S
  Y1
  O
  L1
  V1
  C
  A
  S1
  U1
  Z
  K1
  A2
  N
  R1
  N1
  M
  D
  T1
  J
  W1
  I)
        (and (= v_55 T)
     (= v_56 B1)
     (= v_57 Q)
     (= v_58 F1)
     (= G1 1)
     (= v_59 T)
     (= v_60 B1)
     (= v_61 Q)
     (= v_62 F1))
      )
      (|<Main: void main(JayArray_java_lang_String)>_Block13_1|
  T
  B1
  Q
  F1
  M1
  H
  P1
  E1
  D1
  C1
  G
  K
  X
  Z1
  A1
  J1
  C2
  B2
  Y
  E
  W
  U
  P
  v_59
  v_60
  v_61
  v_62
  R
  H1
  V
  X1
  B
  S
  Y1
  O
  L1
  G1
  C
  A
  S1
  U1
  K1
  A2
  N
  R1
  N1
  M
  D
  T1
  J
  W1
  I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (v_48 Int) (v_49 Int) (v_50 Int) (v_51 Int) (v_52 Int) (v_53 Int) (v_54 Int) (v_55 Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_Block13_1|
  B1
  E
  S
  N
  W
  F
  H1
  Q1
  V
  T
  R
  S1
  E1
  P
  X
  K
  Z
  I
  B
  U
  Q
  F1
  D1
  v_48
  v_49
  v_50
  v_51
  V1
  H
  I1
  L1
  D
  R1
  P1
  M
  A1
  C1
  O1
  O
  C
  N1
  L
  G1
  Y
  M1
  G
  U1
  J
  A
  J1
  T1
  K1)
        (and (= v_48 B1)
     (= v_49 E)
     (= v_50 S)
     (= v_51 N)
     (= B1 1)
     (<= 0 N)
     (= E 137)
     (= v_52 B1)
     (= v_53 E)
     (= v_54 S)
     (= v_55 N))
      )
      (|<Main: void main(JayArray_java_lang_String)>_Block13_2|
  B1
  E
  S
  N
  W
  F
  H1
  Q1
  V
  T
  R
  S1
  E1
  P
  X
  K
  Z
  I
  B
  U
  Q
  F1
  D1
  v_52
  v_53
  v_54
  v_55
  V1
  H
  I1
  L1
  D
  R1
  P1
  M
  C1
  O1
  O
  C
  N1
  L
  G1
  Y
  M1
  G
  U1
  J
  A
  J1
  T1
  K1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (v_49 Int) (v_50 Int) (v_51 Int) (v_52 Int) (v_53 Int) (v_54 Int) (v_55 Int) (v_56 Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_Block13_2|
  N
  L1
  F
  X
  Q1
  B1
  O
  C
  V
  S1
  E1
  U1
  D1
  C1
  W
  J
  Z
  Q
  M
  B
  K1
  W1
  G1
  v_49
  v_50
  v_51
  v_52
  E
  T1
  L
  U
  I
  M1
  D
  Y
  N1
  F1
  V1
  G
  T
  R
  H
  A
  I1
  P1
  K
  J1
  S
  A1
  H1
  P)
        (and (= v_49 N)
     (= v_50 L1)
     (= v_51 F)
     (= v_52 X)
     (= R1 1)
     (= v_53 N)
     (= v_54 L1)
     (= v_55 F)
     (= v_56 X))
      )
      (|<Main: void main(JayArray_java_lang_String)>_Block13_3|
  N
  L1
  F
  X
  Q1
  B1
  O
  C
  V
  S1
  E1
  U1
  D1
  C1
  W
  J
  B
  K1
  W1
  G1
  v_53
  v_54
  v_55
  v_56
  E
  T1
  L
  U
  I
  M1
  D
  Y
  N1
  F1
  V1
  G
  T
  O1
  R1
  A
  I1
  P1
  K
  J1
  S
  A1
  H1
  P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (v_44 Int) (v_45 Int) (v_46 Int) (v_47 Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_Block13_3|
  H
  B1
  L
  N
  P
  F
  Z
  O1
  O
  Q
  I1
  N1
  Q1
  A1
  T
  W
  S
  H1
  V
  M1
  v_44
  v_45
  v_46
  v_47
  R1
  U
  C1
  Y
  B
  J
  G
  L1
  E1
  P1
  M
  R
  F1
  K
  G1
  K1
  D1
  E
  A
  I
  J1
  X
  C
  D)
        (and (= v_44 H) (= v_45 B1) (= v_46 L) (= v_47 N) (= H 1))
      )
      (|<Main: void main(JayArray_java_lang_String)>_Block13_4|
  H
  B1
  L
  N
  P
  F
  Z
  O1
  O
  Q
  I1
  N1
  Q1
  A1
  T
  W
  S
  H1
  V
  M1
  R1
  U
  C1
  Y
  B
  J
  G
  L1
  E1
  K
  G1
  M
  R
  F1
  A
  I
  J1
  X
  C
  D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_Block13_4|
  G1
  H
  E1
  K
  A
  L1
  F1
  D1
  N1
  K1
  C
  I
  Z
  V
  M1
  R
  G
  U
  L
  O
  T
  J1
  J
  O1
  X
  B1
  S
  C1
  M
  F
  Q
  H1
  A1
  B
  W
  E
  Y
  I1
  P
  D)
        true
      )
      (|<Main: void main(JayArray_java_lang_String)>_Block13_5|
  G1
  H
  E1
  K
  A
  L1
  F1
  D1
  N1
  K1
  C
  I
  Z
  V
  M1
  R
  G
  U
  L
  O
  T
  J1
  J
  O1
  X
  B1
  S
  C1
  M
  N
  F
  Q
  H1
  A1
  B
  W
  E
  Y
  I1
  P
  D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_Block13_5|
  N
  Q
  G1
  Z
  O
  U
  M
  H
  C1
  J
  O1
  M1
  P
  W
  H1
  L1
  L
  F
  I1
  K
  B1
  A
  J1
  X
  Y
  E1
  D1
  G
  T
  P1
  I
  F1
  C
  E
  D
  R
  K1
  V
  A1
  N1
  B)
        (= S 0)
      )
      (|<Main: void main(JayArray_java_lang_String)>_Block13_6|
  N
  Q
  G1
  Z
  O
  U
  M
  H
  C1
  J
  O1
  M1
  P
  W
  H1
  L1
  L
  F
  I1
  K
  S
  B1
  A
  J1
  X
  Y
  E1
  D1
  G
  T
  P1
  I
  F1
  C
  E
  D
  R
  K1
  V
  A1
  N1
  B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_Block13_6|
  J1
  R
  B
  N
  A1
  L1
  Z
  C
  H
  H1
  L
  K
  A
  O1
  W
  E1
  X
  S
  Q
  I1
  Y
  K1
  N1
  M
  G1
  G
  T
  F1
  D
  B1
  P
  V
  D1
  E
  F
  J
  I
  C1
  U
  P1
  M1
  O)
        (not (= Y 0))
      )
      |Assert #0: Main.java, line 13|
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        true
      )
      (|<Main: void main(JayArray_java_lang_String)>_pre|
  P
  L
  J
  B
  M
  F
  O
  G
  N
  H
  I
  K
  E
  A
  D
  C)
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        |Assert #0: Main.java, line 13|
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
