(set-logic HORN)


(declare-fun |main@entry| ( ) Bool)
(declare-fun |main@tailrecurse.i3| ( Bool Int Int ) Bool)
(declare-fun |main@A.exit4.split| ( ) Bool)
(declare-fun |main@tailrecurse.i| ( Bool Int Int Int Int ) Bool)

(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        true
      )
      main@entry
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Int) (E Bool) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        main@entry
        (and (= G (ite E 1 0))
     (or (not C) (not B) (= A F))
     (or (not C) (not B) (= D G))
     (or (not C) (not B) (= H A))
     (or (not C) (not B) (= I D))
     (or (not B) (and C B))
     (= B true)
     (= E (= F 0)))
      )
      (main@tailrecurse.i E F G H I)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Bool) (F Bool) (G Int) (H Bool) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (main@tailrecurse.i H I J C B)
        (and (or (not F) (not E) (= D B))
     (or (not F) (not E) (= G C))
     (or (not F) (not E) (= K D))
     (or (not F) (not E) (= L G))
     (or (not F) (not E) (not A))
     (or (not E) (and F E))
     (= E true)
     (= A (= C 0)))
      )
      (main@tailrecurse.i H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) (F Int) (G Int) (H Bool) (I Bool) (J Int) (K Bool) (L Int) (M Int) ) 
    (=>
      (and
        (main@tailrecurse.i K E F B A)
        (and (or D (not I) (not C))
     (or (not I) (not H) (= G E))
     (or (not I) (not H) (= J F))
     (or (not I) (not H) (= L G))
     (or (not I) (not H) (= M J))
     (or (not H) (and I H))
     (or (not I) (and I C))
     (= H true)
     (= D (= B 0)))
      )
      (main@tailrecurse.i3 K L M)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Bool) (F Bool) (G Int) (H Bool) (I Int) (J Int) ) 
    (=>
      (and
        (main@tailrecurse.i3 H C B)
        (and (or (not F) (not E) (= D B))
     (or (not F) (not E) (= G C))
     (or (not F) (not E) (= I D))
     (or (not F) (not E) (= J G))
     (or (not F) (not E) (not A))
     (or (not E) (and F E))
     (= E true)
     (= A (= C 0)))
      )
      (main@tailrecurse.i3 H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) ) 
    (=>
      (and
        (main@tailrecurse.i3 E B A)
        (and (or (not F) (not C) D)
     (or (not F) (and F C))
     (or (not F) (not E))
     (or (not G) (and G F))
     (= G true)
     (= D (= B 0)))
      )
      main@A.exit4.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@A.exit4.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
