; ./prepared/synth/semgus/./nthbit.CLIA_Track_Const__sum_3_5__1_2_000.smt2
(set-logic HORN)


(declare-fun |funcStartBool__syn| ( (Array Int Int) Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool (Array Int Int) Int Bool Bool Bool Bool ) Bool)
(declare-fun |funcStart__syn| ( (Array Int Int) Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool (Array Int Int) Int Bool Bool Bool Bool ) Bool)
(declare-fun |realizable| ( ) Bool)
(declare-fun |funcmainStart__syn| ( (Array Int Int) Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool (Array Int Int) Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool ) Bool)

(assert
  (forall ( (A Int) (B (Array Int Int)) (C Bool) (D Bool) (E Bool) (F Bool) (G (Array Int Int)) (H Int) (I (Array Int Int)) (J Int) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Bool) (v_32 Bool) (v_33 Bool) (v_34 Bool) (v_35 Bool) (v_36 Bool) (v_37 Bool) (v_38 Bool) (v_39 Bool) (v_40 Bool) (v_41 Bool) (v_42 Bool) (v_43 Bool) ) 
    (=>
      (and
        (funcStart__syn B A M X L O P Q R S T U W Z A1 B1 C1 D1 E1 F1 I J K N V Y)
        (and (= B (store G H 0))
     (= E (ite M N O))
     (= F (ite M K L))
     (= C (ite X Y Z))
     (= D (ite X V W))
     (= A (+ 1 H))
     (= v_32 P)
     (= v_33 Q)
     (= v_34 R)
     (= v_35 S)
     (= v_36 T)
     (= v_37 U)
     (= v_38 A1)
     (= v_39 B1)
     (= v_40 C1)
     (= v_41 D1)
     (= v_42 E1)
     (= v_43 F1))
      )
      (funcmainStart__syn
  G
  H
  M
  X
  L
  O
  P
  Q
  R
  S
  T
  U
  W
  Z
  A1
  B1
  C1
  D1
  E1
  F1
  I
  J
  F
  E
  v_32
  v_33
  v_34
  v_35
  v_36
  v_37
  D
  C
  v_38
  v_39
  v_40
  v_41
  v_42
  v_43)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Bool) (D Bool) (E Bool) (F Bool) (G (Array Int Int)) (H Int) (I Bool) (J Bool) (K Bool) (L Bool) (M (Array Int Int)) (N Int) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Bool) (G1 (Array Int Int)) (H1 Int) (v_34 Bool) (v_35 Bool) (v_36 Bool) (v_37 Bool) ) 
    (=>
      (and
        (funcStart__syn G H O P Q R S T U V W X Y Z A1 B1 C1 D1 E1 F1 G1 H1 I J K L)
        (funcStart__syn B A O P Q R S T U V W X Y Z A1 B1 C1 D1 E1 F1 G H C D E F)
        (and (= B (store M N 11))
     (= A (+ 1 N))
     (= v_34 true)
     (= v_35 true)
     (= v_36 true)
     (= v_37 true))
      )
      (funcStartBool__syn
  M
  N
  O
  P
  Q
  R
  S
  T
  U
  V
  W
  X
  Y
  Z
  A1
  B1
  C1
  D1
  E1
  F1
  G1
  H1
  v_34
  v_35
  v_36
  v_37)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Bool) (D Bool) (E Bool) (F Bool) (G (Array Int Int)) (H Int) (I (Array Int Int)) (J Int) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) (C1 (Array Int Int)) (D1 Int) (E1 Bool) (F1 Bool) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) ) 
    (=>
      (and
        (funcStartBool__syn G H K L M N O P Q R S T U V W X Y Z A1 B1 C1 D1 F1 H1 J1 L1)
        (funcStartBool__syn B A K L M N O P Q R S T U V W X Y Z A1 B1 G H E1 G1 I1 K1)
        (and (= B (store I J 10))
     (= E (or H1 G1))
     (= F (and F1 E1))
     (= D (and J1 I1))
     (= C (or L1 K1))
     (= A (+ 1 J)))
      )
      (funcStartBool__syn I J K L M N O P Q R S T U V W X Y Z A1 B1 C1 D1 F E D C)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Bool) (D Bool) (E Bool) (F Bool) (G (Array Int Int)) (H Int) (I (Array Int Int)) (J Int) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) (C1 (Array Int Int)) (D1 Int) (E1 Bool) (F1 Bool) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) ) 
    (=>
      (and
        (funcStartBool__syn G H K L M N O P Q R S T U V W X Y Z A1 B1 C1 D1 F1 H1 J1 L1)
        (funcStartBool__syn B A K L M N O P Q R S T U V W X Y Z A1 B1 G H E1 G1 I1 K1)
        (and (= B (store I J 12))
     (= E (or H1 G1))
     (= F (or F1 E1))
     (= D (or J1 I1))
     (= C (or L1 K1))
     (= A (+ 1 J)))
      )
      (funcStartBool__syn I J K L M N O P Q R S T U V W X Y Z A1 B1 C1 D1 F E D C)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Bool) (D Bool) (E (Array Int Int)) (F Int) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y (Array Int Int)) (Z Int) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Bool) ) 
    (=>
      (and
        (funcStartBool__syn B A G H I J K L M N O P Q R S T U V W X Y Z A1 B1 C1 D1)
        (and (= B (store E F 13)) (not (= A1 D)) (not (= C1 C)) (= A (+ 1 F)))
      )
      (funcStartBool__syn E F G H I J K L M N O P Q R S T U V W X Y Z D B1 C D1)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U (Array Int Int)) (V Int) (v_22 Bool) (v_23 Bool) (v_24 Bool) (v_25 Bool) ) 
    (=>
      (and
        (and (= (store A B 6) U)
     (= B (+ (- 1) V))
     (= v_22 true)
     (= v_23 false)
     (= v_24 true)
     (= v_25 false))
      )
      (funcStart__syn A B C D E F G H I J K L M N O P Q R S T U V v_22 v_23 v_24 v_25)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Bool) (D Bool) (E Bool) (F Bool) (G (Array Int Int)) (H Int) (I Bool) (J Bool) (K Bool) (L Bool) (M (Array Int Int)) (N Int) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Bool) (G1 (Array Int Int)) (H1 Int) (v_34 Bool) (v_35 Bool) (v_36 Bool) (v_37 Bool) ) 
    (=>
      (and
        (funcStart__syn G H O P Q R S T U V W X Y Z A1 B1 C1 D1 E1 F1 G1 H1 I J K L)
        (funcStart__syn B A O P Q R S T U V W X Y Z A1 B1 C1 D1 E1 F1 G H C D E F)
        (and (= B (store M N 5))
     (= A (+ 1 N))
     (= v_34 true)
     (= v_35 true)
     (= v_36 true)
     (= v_37 true))
      )
      (funcStart__syn M
                N
                O
                P
                Q
                R
                S
                T
                U
                V
                W
                X
                Y
                Z
                A1
                B1
                C1
                D1
                E1
                F1
                G1
                H1
                v_34
                v_35
                v_36
                v_37)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q (Array Int Int)) (R Int) (S Bool) (T Bool) (U Bool) (V Bool) (v_22 Bool) (v_23 Bool) (v_24 Bool) (v_25 Bool) ) 
    (=>
      (and
        (and (= (store A B 8) Q)
     (= B (+ (- 1) R))
     (= v_22 S)
     (= v_23 T)
     (= v_24 U)
     (= v_25 V))
      )
      (funcStart__syn A B C D E F S T G H I J K L U V M N O P Q R v_22 v_23 v_24 v_25)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q (Array Int Int)) (R Int) (S Bool) (T Bool) (U Bool) (V Bool) (v_22 Bool) (v_23 Bool) (v_24 Bool) (v_25 Bool) ) 
    (=>
      (and
        (and (= (store A B 4) Q)
     (= B (+ (- 1) R))
     (= v_22 S)
     (= v_23 T)
     (= v_24 U)
     (= v_25 V))
      )
      (funcStart__syn A B C D E F G H I J S T K L M N O P U V Q R v_22 v_23 v_24 v_25)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q (Array Int Int)) (R Int) (S Bool) (T Bool) (U Bool) (V Bool) (v_22 Bool) (v_23 Bool) (v_24 Bool) (v_25 Bool) ) 
    (=>
      (and
        (and (= (store A B 3) Q)
     (= B (+ (- 1) R))
     (= v_22 S)
     (= v_23 T)
     (= v_24 U)
     (= v_25 V))
      )
      (funcStart__syn A B C D E F G H S T I J K L M N U V O P Q R v_22 v_23 v_24 v_25)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D (Array Int Int)) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K (Array Int Int)) (L Int) (M (Array Int Int)) (N Int) (O (Array Int Int)) (P Int) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Bool) (G1 Bool) (H1 Bool) (I1 (Array Int Int)) (J1 Int) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Bool) (R1 Bool) (S1 Bool) (T1 Bool) (U1 Bool) (V1 Bool) (W1 Bool) (X1 Bool) ) 
    (=>
      (and
        (funcStart__syn M
                N
                F
                E
                S
                T
                U
                V
                W
                X
                Y
                Z
                A1
                B1
                C1
                D1
                E1
                F1
                G1
                H1
                I1
                J1
                O1
                Q1
                V1
                X1)
        (funcStartBool__syn
  D
  C
  Q
  R
  S
  T
  U
  V
  W
  X
  Y
  Z
  A1
  B1
  C1
  D1
  E1
  F1
  G1
  H1
  K
  L
  M1
  K1
  T1
  R1)
        (funcStart__syn K L B A S T U V W X Y Z A1 B1 C1 D1 E1 F1 G1 H1 M N N1 P1 U1 W1)
        (let ((a!1 (= F (and Q (not (ite K1 L1 M1)))))
      (a!2 (= E (and R (not (ite R1 S1 T1))))))
  (and (= D (store O P 7))
       (= J (ite (ite K1 L1 M1) N1 O1))
       (= I (or Q1 P1))
       (= H (ite (ite R1 S1 T1) U1 V1))
       (= G (or X1 W1))
       a!1
       a!2
       (= B (and Q (ite K1 L1 M1)))
       (= A (and R (ite R1 S1 T1)))
       (= C (+ 1 P))))
      )
      (funcStart__syn O P Q R S T U V W X Y Z A1 B1 C1 D1 E1 F1 G1 H1 I1 J1 J I H G)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I (Array Int Int)) (J (Array Int Int)) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Bool) (G1 Bool) (v_33 Int) (v_34 Bool) (v_35 Bool) (v_36 Bool) (v_37 Bool) (v_38 Bool) (v_39 Bool) (v_40 Bool) (v_41 Bool) (v_42 Bool) (v_43 Bool) (v_44 Bool) (v_45 Bool) (v_46 Bool) (v_47 Bool) (v_48 Bool) (v_49 Bool) (v_50 Bool) (v_51 Bool) ) 
    (=>
      (and
        (funcmainStart__syn
  I
  v_33
  v_34
  v_35
  v_36
  v_37
  v_38
  v_39
  v_40
  v_41
  v_42
  v_43
  v_44
  v_45
  v_46
  v_47
  v_48
  v_49
  v_50
  v_51
  J
  K
  H
  M
  G
  P
  F
  S
  E
  V
  D
  X
  C
  A1
  B
  D1
  A
  G1)
        (and (= 0 v_33)
     (= v_34 true)
     (= v_35 true)
     (= v_36 true)
     (= v_37 false)
     (= v_38 false)
     (= v_39 false)
     (= v_40 false)
     (= v_41 false)
     (= v_42 false)
     (= v_43 false)
     (= v_44 true)
     (= v_45 false)
     (= v_46 true)
     (= v_47 false)
     (= v_48 false)
     (= v_49 false)
     (= v_50 false)
     (= v_51 false)
     (= F (ite S Q R))
     (= G (ite P N O))
     (= B (ite D1 B1 C1))
     (= C (ite A1 Y Z))
     (= D (or (not X) W))
     (= E (ite V T U))
     (= H (and M L))
     (= A (ite G1 E1 F1)))
      )
      realizable
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        realizable
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
