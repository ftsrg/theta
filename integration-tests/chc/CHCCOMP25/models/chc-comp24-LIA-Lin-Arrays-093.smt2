(set-logic HORN)


(declare-fun |INV_MAIN_0| ( Int Int (Array Int Int) Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (and (= B E) (= A D) (= C F))
      )
      (INV_MAIN_0 A B C E D F)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D (Array Int Int)) (E Int) (F Int) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Int) (L (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 G H I J K L)
        (and (= D (store I G (select I H)))
     (not (= (select L J) 0))
     (not (= (select I H) 0))
     (= B (+ 1 K))
     (= C (+ 1 J))
     (= E (+ 1 H))
     (= F (+ 1 G))
     (= A (store L K (select L J))))
      )
      (INV_MAIN_0 F E D C B A)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 D E F G H I)
        (and (= (select I G) 0)
     (not (= (select F E) 0))
     (= B (+ 1 E))
     (= C (+ 1 D))
     (= A (store F D (select F E))))
      )
      (INV_MAIN_0 C B A G H I)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 D E F G H I)
        (and (not (= (select I G) 0))
     (= (select F E) 0)
     (= B (+ 1 H))
     (= C (+ 1 G))
     (= A (store I H (select I G))))
      )
      (INV_MAIN_0 D E F C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (Array Int Int)) (D Int) (E Int) (F (Array Int Int)) ) 
    (=>
      (and
        (INV_MAIN_0 A B C D E F)
        (let ((a!1 (not (= (store C A (select C B)) (store F E (select F D))))))
  (and (= (select C B) 0) (or (not (= A E)) a!1) (= (select F D) 0)))
      )
      false
    )
  )
)

(check-sat)
(exit)
