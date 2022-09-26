; synthesis/nay-horn/./PLUS_array_search_2_000.smt2
(set-logic HORN)

(declare-fun |NT1| ( Int Int Int Int ) Bool)
(declare-fun |NT4| ( Bool Bool Bool Bool ) Bool)
(declare-fun |NT7| ( Bool Bool Bool Bool ) Bool)
(declare-fun |NT3| ( Int Int Int Int ) Bool)
(declare-fun |Start| ( Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (NT1 A B C D)
        true
      )
      (Start A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (NT3 A B C D)
        true
      )
      (Start A B C D)
    )
  )
)
(assert
  (forall ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) ) 
    (=>
      (and
        (and true (= (- 1) v_0) (= 0 v_1) (= (- 1) v_2) (= (- 2) v_3))
      )
      (NT1 v_0 v_1 v_2 v_3)
    )
  )
)
(assert
  (forall ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) ) 
    (=>
      (and
        (and true (= (- 1) v_0) (= 2 v_1) (= 0 v_2) (= (- 1) v_3))
      )
      (NT1 v_0 v_1 v_2 v_3)
    )
  )
)
(assert
  (forall ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) ) 
    (=>
      (and
        (and true (= 0 v_0) (= 0 v_1) (= 0 v_2) (= 0 v_3))
      )
      (NT1 v_0 v_1 v_2 v_3)
    )
  )
)
(assert
  (forall ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) ) 
    (=>
      (and
        (and true (= (- 2) v_0) (= 1 v_1) (= 1 v_2) (= (- 3) v_3))
      )
      (NT1 v_0 v_1 v_2 v_3)
    )
  )
)
(assert
  (forall ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) ) 
    (=>
      (and
        (and true (= 1 v_0) (= 1 v_1) (= 1 v_2) (= 1 v_3))
      )
      (NT1 v_0 v_1 v_2 v_3)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (G Bool) (H Bool) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        (NT1 M N O P)
        (NT4 E F G H)
        (NT1 I J K L)
        (and (= B (ite G K O)) (= C (ite F J N)) (= D (ite E I M)) (= A (ite H L P)))
      )
      (NT1 D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (NT1 I J K L)
        (NT1 E F G H)
        (and (= B (+ G K)) (= C (+ F J)) (= D (+ E I)) (= A (+ H L)))
      )
      (NT3 D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (G Bool) (H Bool) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        (NT1 M N O P)
        (NT4 E F G H)
        (NT3 I J K L)
        (and (= B (ite G K O)) (= C (ite F J N)) (= D (ite E I M)) (= A (ite H L P)))
      )
      (NT3 D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (G Bool) (H Bool) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        (NT3 M N O P)
        (NT4 E F G H)
        (NT1 I J K L)
        (and (= B (ite G K O)) (= C (ite F J N)) (= D (ite E I M)) (= A (ite H L P)))
      )
      (NT3 D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Bool) (G Bool) (H Bool) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        (NT1 M N O P)
        (NT7 E F G H)
        (NT1 I J K L)
        (and (= B (ite G K O)) (= C (ite F J N)) (= D (ite E I M)) (= A (ite H L P)))
      )
      (NT3 D C B A)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (NT1 I J K L)
        (NT1 E F G H)
        (and (= C (>= F J)) (= B (>= G K)) (= A (>= H L)) (= D (>= E I)))
      )
      (NT4 D C B A)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) ) 
    (=>
      (and
        (NT4 I J K L)
        (NT4 E F G H)
        (and (= C (and F J)) (= B (and G K)) (= A (and H L)) (= D (and E I)))
      )
      (NT4 D C B A)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (NT1 I J K L)
        (NT3 E F G H)
        (and (= C (>= F J)) (= B (>= G K)) (= A (>= H L)) (= D (>= E I)))
      )
      (NT7 D C B A)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) ) 
    (=>
      (and
        (NT4 I J K L)
        (NT7 E F G H)
        (and (= C (and F J)) (= B (and G K)) (= A (and H L)) (= D (and E I)))
      )
      (NT7 D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (Start A B C D)
        (and (= C 3) (= B 2) (= A 0) (= D 1))
      )
      false
    )
  )
)

(check-sat)
(exit)
