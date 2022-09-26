; vmt-chc-benchmarks/./ctigar/nest-len.c_000.smt2
(set-logic HORN)

(declare-fun |state| ( Bool Bool Bool Bool Bool Bool Int Int Int Int ) Bool)

(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Int) (G Int) (H Int) (I Int) (J Bool) ) 
    (=>
      (and
        (and (= D true) (not C) (not B) (not J) (not A) (not E))
      )
      (state E D C A B J I H G F)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Bool) ) 
    (=>
      (and
        (state E D C A B T S Q O M)
        (let ((a!1 (and K
                (not J)
                (not I)
                H
                (not G)
                (not F)
                (= M L)
                (= O N)
                (= Q P)
                (= S R)))
      (a!2 (and K
                (not J)
                (not I)
                (not H)
                (not G)
                F
                (= O N)
                (= Q P)
                (= S R)
                (= (+ M (* (- 1) L)) (- 1))))
      (a!3 (and (not K)
                J
                I
                H
                (not G)
                F
                (= O N)
                (= Q P)
                (= S R)
                (= (+ M (* (- 1) L)) (- 1))))
      (a!4 (and (not K)
                J
                I
                (not H)
                (not G)
                F
                (= O N)
                (= Q P)
                (= S R)
                (= (+ M (* (- 1) L)) (- 1))))
      (a!5 (and (not K)
                J
                (not I)
                H
                (not G)
                F
                (= O N)
                (= Q P)
                (= S R)
                (= (+ M (* (- 1) L)) (- 1))))
      (a!6 (and (not K)
                J
                (not I)
                (not H)
                (not G)
                F
                (= O N)
                (= Q P)
                (= S R)
                (= (+ M (* (- 1) L)) (- 1))))
      (a!7 (and (not K)
                (not J)
                I
                H
                (not G)
                F
                (= O N)
                (= Q P)
                (= S R)
                (= (+ M (* (- 1) L)) (- 1))))
      (a!8 (and (not K)
                (not J)
                I
                (not H)
                (not G)
                F
                (= O N)
                (= Q P)
                (= S R)
                (= (+ M (* (- 1) L)) (- 1))))
      (a!9 (and K
                (not J)
                (not I)
                (not H)
                G
                F
                (= M L)
                (= Q P)
                (= S R)
                (= (+ O (* (- 1) N)) (- 1))))
      (a!10 (and (not K)
                 (not J)
                 (not I)
                 (not H)
                 (not G)
                 (not F)
                 (= M L)
                 (= O N)
                 (= Q P)
                 (= S R))))
  (and (or A B C (not D) (not E) T a!1 (<= 1 O))
       (or (not A)
           (not B)
           (not C)
           (not D)
           (not E)
           T
           (and K
                (not J)
                (not I)
                (not H)
                G
                (not F)
                (= M L)
                (= O N)
                (= Q P)
                (= S R))
           (not (<= S M)))
       (or (not A)
           (not B)
           (not C)
           (not D)
           (not E)
           T
           (and K
                (not J)
                (not I)
                (not H)
                (not G)
                (not F)
                (= M L)
                (= O N)
                (= Q P)
                (= S R))
           (<= S M))
       (or (not A)
           (not B)
           C
           (not D)
           (not E)
           T
           (and (not K) J I H G (not F) (= M L) (= O N) (= Q P) (= S R))
           (not (<= S M)))
       (or (not A)
           (not B)
           C
           (not D)
           (not E)
           T
           (and (not K) J I H (not G) (not F) (= M L) (= O N) (= Q P) (= S R))
           (<= S M))
       (or A
           (not B)
           (not C)
           (not D)
           (not E)
           T
           (and (not K) J I (not H) G (not F) (= M L) (= O N) (= Q P) (= S R))
           (not (<= S M)))
       (or A
           (not B)
           (not C)
           (not D)
           (not E)
           T
           (and (not K)
                J
                I
                (not H)
                (not G)
                (not F)
                (= M L)
                (= O N)
                (= Q P)
                (= S R))
           (<= S M))
       (or A
           (not B)
           C
           (not D)
           (not E)
           T
           (and (not K) J (not I) H G (not F) (= M L) (= O N) (= Q P) (= S R))
           (not (<= S M)))
       (or A
           (not B)
           C
           (not D)
           (not E)
           T
           (and (not K)
                J
                (not I)
                H
                (not G)
                (not F)
                (= M L)
                (= O N)
                (= Q P)
                (= S R))
           (<= S M))
       (or (not A)
           B
           (not C)
           (not D)
           (not E)
           T
           (and (not K)
                J
                (not I)
                (not H)
                G
                (not F)
                (= M L)
                (= O N)
                (= Q P)
                (= S R))
           (not (<= S M)))
       (or (not A)
           B
           (not C)
           (not D)
           (not E)
           T
           (and (not K)
                J
                (not I)
                (not H)
                (not G)
                (not F)
                (= M L)
                (= O N)
                (= Q P)
                (= S R))
           (<= S M))
       (or (not A)
           B
           C
           (not D)
           (not E)
           T
           (and (not K) (not J) I H G (not F) (= M L) (= O N) (= Q P) (= S R))
           (not (<= S M)))
       (or (not A)
           B
           C
           (not D)
           (not E)
           T
           (and (not K)
                (not J)
                I
                H
                (not G)
                (not F)
                (= M L)
                (= O N)
                (= Q P)
                (= S R))
           (<= S M))
       (or A
           B
           (not C)
           (not D)
           (not E)
           T
           (and (not K)
                (not J)
                I
                (not H)
                G
                (not F)
                (= M L)
                (= O N)
                (= Q P)
                (= S R))
           (not (<= S M)))
       (or A
           B
           (not C)
           (not D)
           (not E)
           T
           (and (not K)
                (not J)
                I
                (not H)
                (not G)
                (not F)
                (= M L)
                (= O N)
                (= Q P)
                (= S R))
           (<= S M))
       (or A
           B
           C
           (not D)
           (not E)
           T
           (and (not K)
                (not J)
                (not I)
                H
                (not G)
                (not F)
                (= M L)
                (= O N)
                (= Q P)
                (= S R))
           (not (<= 1 O)))
       (or A
           B
           C
           D
           (not E)
           T
           (and (not K)
                (not J)
                (not I)
                (not H)
                G
                F
                (= M L)
                (= O N)
                (= Q P)
                (= S R))
           (<= S O))
       (or A B C D E (not T) a!2)
       (or (not A) (not B) (not C) D E T a!3)
       (or (not A) (not B) C D E T a!4)
       (or A (not B) (not C) D E T a!5)
       (or A (not B) C D E T a!6)
       (or (not A) B (not C) D E T a!7)
       (or (not A) B C D E T a!8)
       (or A B C D (not E) (not T) a!9)
       (or A B (not C) D E (not T) a!1)
       (or A
           B
           C
           (not D)
           E
           (not T)
           (and (not K) J I H G F (= M L) (= O N) (= Q P) (= S R)))
       (or (not A)
           (not B)
           (not C)
           (not D)
           E
           T
           (and (not K) J I (not H) G F (= M L) (= O N) (= Q P) (= S R)))
       (or (not A)
           (not B)
           C
           (not D)
           E
           T
           (and (not K) J (not I) H G F (= M L) (= O N) (= Q P) (= S R)))
       (or A
           (not B)
           (not C)
           (not D)
           E
           T
           (and (not K) J (not I) (not H) G F (= M L) (= O N) (= Q P) (= S R)))
       (or A
           (not B)
           C
           (not D)
           E
           T
           (and (not K) (not J) I H G F (= M L) (= O N) (= Q P) (= S R)))
       (or (not A)
           B
           (not C)
           (not D)
           E
           T
           (and (not K) (not J) I (not H) G F (= M L) (= O N) (= Q P) (= S R)))
       (or (not A)
           B
           C
           (not D)
           E
           T
           (and (not K) (not J) (not I) H G F (= M L) (= O N) (= Q P) (= S R)))
       (or A
           B
           (not C)
           D
           E
           T
           (and (not K)
                (not J)
                (not I)
                H
                (not G)
                F
                (= M L)
                (= O N)
                (= Q P)
                (= S R)))
       (or A
           B
           C
           (not D)
           (not E)
           (not T)
           (and (not K)
                (not J)
                (not I)
                (not H)
                G
                (not F)
                (= M L)
                (= O N)
                (= Q P)
                (= S R)))
       (or A B C D E T a!10)
       (or A B (not C) (not D) E (not T) a!10)
       (or (not A)
           (not B)
           (not C)
           D
           (not E)
           T
           (and (not K) J I H G F (= L 1) (= O N) (= Q P) (= S R)))
       (or (not A)
           (not B)
           C
           D
           (not E)
           T
           (and (not K) J I (not H) G F (= L 1) (= O N) (= Q P) (= S R)))
       (or A
           (not B)
           (not C)
           D
           (not E)
           T
           (and (not K) J (not I) H G F (= L 1) (= O N) (= Q P) (= S R)))
       (or A
           (not B)
           C
           D
           (not E)
           T
           (and (not K) J (not I) (not H) G F (= L 1) (= O N) (= Q P) (= S R)))
       (or (not A)
           B
           (not C)
           D
           (not E)
           T
           (and (not K) (not J) I H G F (= L 1) (= O N) (= Q P) (= S R)))
       (or (not A)
           B
           C
           D
           (not E)
           T
           (and (not K) (not J) I (not H) G F (= L 1) (= O N) (= Q P) (= S R)))
       (or A
           B
           (not C)
           D
           (not E)
           T
           (and (not K) (not J) (not I) H G F (= L 1) (= O N) (= Q P) (= S R)))
       (or A
           B
           (not C)
           (not D)
           E
           T
           (and (not K)
                (not J)
                (not I)
                H
                G
                (not F)
                (= L 1)
                (= O N)
                (= Q P)
                (= S R)))
       (or A
           B
           C
           (not D)
           E
           T
           (and (not K)
                (not J)
                (not I)
                (not H)
                G
                (not F)
                (= N 1)
                (= M L)
                (= Q P)
                (= S R)))
       (or A
           B
           C
           D
           (not E)
           T
           (and K (not J) (not I) H (not G) F (= M L) (= O N) (= Q P) (= S R))
           (not (<= S O)))))
      )
      (state G F H I J K R P N L)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Int) (G Int) (H Int) (I Int) (J Bool) ) 
    (=>
      (and
        (state E D C A B J I H G F)
        (and (not D) (= C true) (not B) (= J true) (not A) (not E))
      )
      false
    )
  )
)

(check-sat)
(exit)
