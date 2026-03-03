(set-logic HORN)


(declare-fun |<Main: void main(JayArray_java_lang_String)>_Block6_3| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |<Main: void main(JayArray_java_lang_String)>_Block6_6| ( Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |Assert #0: Main.java, line 13| ( ) Bool)
(declare-fun |<Main: void main(JayArray_java_lang_String)>_Block6_4| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |<Main: void main(JayArray_java_lang_String)>_Block3| ( Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |<Main: void main(JayArray_java_lang_String)>_Block6_8| ( Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |<Main: void main(JayArray_java_lang_String)>_Block6_5| ( Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |<Main: void main(JayArray_java_lang_String)>_Block6_2| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |Assert #1: Main.java, line 16| ( ) Bool)
(declare-fun |<Main: void main(JayArray_java_lang_String)>_Block6_7| ( Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |<Main: void main(JayArray_java_lang_String)>_Block6_9| ( Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |<Main: void main(JayArray_java_lang_String)>_Block4| ( Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |<Main: void main(JayArray_java_lang_String)>_Block6| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |<Main: void main(JayArray_java_lang_String)>_Block6_1| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |<Main: void main(JayArray_java_lang_String)>_pre| ( Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (v_15 Int) (v_16 Int) (v_17 Int) (v_18 Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_pre| G A E O D)
        (and (= v_15 G) (= v_16 A) (= v_17 E) (= v_18 O))
      )
      (|<Main: void main(JayArray_java_lang_String)>_Block6|
  G
  A
  E
  O
  D
  H
  N
  I
  L
  v_15
  v_16
  v_17
  v_18
  C
  F
  B
  K
  M
  J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (v_16 Int) (v_17 Int) (v_18 Int) (v_19 Int) (v_20 Int) (v_21 Int) (v_22 Int) (v_23 Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_Block6|
  D
  H
  J
  B
  I
  G
  C
  O
  E
  v_16
  v_17
  v_18
  v_19
  N
  F
  K
  M
  A
  L)
        (and (= v_16 D)
     (= v_17 H)
     (= v_18 J)
     (= v_19 B)
     (= P 1)
     (= v_20 D)
     (= v_21 H)
     (= v_22 J)
     (= v_23 B))
      )
      (|<Main: void main(JayArray_java_lang_String)>_Block6_1|
  D
  H
  J
  B
  I
  G
  C
  O
  v_20
  v_21
  v_22
  v_23
  N
  P
  K
  M
  A
  L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (v_14 Int) (v_15 Int) (v_16 Int) (v_17 Int) (v_18 Int) (v_19 Int) (v_20 Int) (v_21 Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_Block6_1|
  J
  M
  G
  A
  I
  D
  E
  C
  v_14
  v_15
  v_16
  v_17
  K
  B
  L
  H
  N
  F)
        (and (= v_14 J)
     (= v_15 M)
     (= v_16 G)
     (= v_17 A)
     (= J 1)
     (<= 0 A)
     (= M 137)
     (= v_18 J)
     (= v_19 M)
     (= v_20 G)
     (= v_21 A))
      )
      (|<Main: void main(JayArray_java_lang_String)>_Block6_2|
  J
  M
  G
  A
  I
  D
  E
  C
  v_18
  v_19
  v_20
  v_21
  B
  L
  H
  N
  F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (v_16 Int) (v_17 Int) (v_18 Int) (v_19 Int) (v_20 Int) (v_21 Int) (v_22 Int) (v_23 Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_Block6_2|
  O
  D
  M
  E
  I
  B
  K
  G
  v_16
  v_17
  v_18
  v_19
  F
  C
  J
  A
  P)
        (and (= v_16 O)
     (= v_17 D)
     (= v_18 M)
     (= v_19 E)
     (= L 0)
     (= H 0)
     (= N 0)
     (= v_20 O)
     (= v_21 D)
     (= v_22 M)
     (= v_23 E))
      )
      (|<Main: void main(JayArray_java_lang_String)>_Block6_3|
  O
  D
  M
  E
  I
  B
  K
  G
  L
  N
  H
  v_20
  v_21
  v_22
  v_23
  F
  C
  J
  A
  P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (v_16 Int) (v_17 Int) (v_18 Int) (v_19 Int) (v_20 Int) (v_21 Int) (v_22 Int) (v_23 Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_Block6_3|
  N
  B
  P
  H
  J
  C
  K
  A
  M
  G
  E
  v_16
  v_17
  v_18
  v_19
  I
  O
  F
  D
  L)
        (and (= v_16 N)
     (= v_17 B)
     (= v_18 P)
     (= v_19 H)
     (= v_20 N)
     (= v_21 B)
     (= v_22 P)
     (= v_23 H))
      )
      (|<Main: void main(JayArray_java_lang_String)>_Block6_4|
  N
  B
  P
  H
  J
  M
  G
  E
  v_20
  v_21
  v_22
  v_23
  I
  O
  F
  D
  L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (v_13 Int) (v_14 Int) (v_15 Int) (v_16 Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_Block6_4|
  G
  E
  D
  F
  J
  L
  I
  M
  v_13
  v_14
  v_15
  v_16
  C
  K
  B
  H
  A)
        (and (= v_13 G) (= v_14 E) (= v_15 D) (= v_16 F))
      )
      (|<Main: void main(JayArray_java_lang_String)>_Block6_5| G E D F J L I M C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_Block6_5| C H J F I E B A G)
        true
      )
      (|<Main: void main(JayArray_java_lang_String)>_Block6_6| C H J F I E B A D G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_Block6_6| A G I F C J B E D H)
        (and (<= D 2147483647) (<= (- 2147483648) D))
      )
      (|<Main: void main(JayArray_java_lang_String)>_Block6_7| A G I F C J B E D H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_Block6_7| A J H D B G E F K C)
        (= I 0)
      )
      (|<Main: void main(JayArray_java_lang_String)>_Block6_8| A J H D B I G E F K C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_Block6_8| E C J F B K I H A D G)
        true
      )
      (|<Main: void main(JayArray_java_lang_String)>_Block6_9| E C J F B I H A D G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_Block6_8| H A F I K G D J C E B)
        (not (= G 0))
      )
      |Assert #0: Main.java, line 13|
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_Block6_9| F E G H B J D A I C)
        (not (<= I 1000))
      )
      (|<Main: void main(JayArray_java_lang_String)>_Block3| F E G H B J D A I C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_Block3| G C F H A B J I E D)
        (not (<= 1001 E))
      )
      (|<Main: void main(JayArray_java_lang_String)>_Block4| G C F H A B J I E D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (|<Main: void main(JayArray_java_lang_String)>_Block4| A J C I E F G B H D)
        true
      )
      |Assert #1: Main.java, line 16|
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        true
      )
      (|<Main: void main(JayArray_java_lang_String)>_pre| C E B D A)
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
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        |Assert #1: Main.java, line 16|
        true
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        CHC_COMP_FALSE
      )
      false
    )
  )
)

(check-sat)
(exit)
