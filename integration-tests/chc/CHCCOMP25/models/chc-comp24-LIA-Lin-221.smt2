(set-logic HORN)


(declare-fun |inv_main101| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |inv_main48| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |inv_main57| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |inv_main2| ( ) Bool)
(declare-fun |inv_main42| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |inv_main78| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |inv_main84| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |inv_main72| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |inv_main24| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |inv_main66| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |inv_main90| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |inv_main54| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |inv_main60| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        true
      )
      inv_main2
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (inv_main66 G D N M O F A K C J E B I H L)
        (= O 0)
      )
      (inv_main72 G D N M O F A K C J E B I H L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        (inv_main66 E M N B O G P F H A K D I L J)
        (and (= G 1) (= C 0) (not (= O 0)))
      )
      (inv_main72 E M N B O C P F H A K D I L J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (inv_main90 B E F I H O A N K G D C M J L)
        (= M 0)
      )
      (inv_main24 B E F I H O A N K G D C M J L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        (inv_main90 D B H C I J A E O G L K N M P)
        (and (= M 1) (= F 0) (not (= N 0)))
      )
      (inv_main24 D B H C I J A E O G L K N F P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        inv_main2
        true
      )
      (inv_main24 L I H O N A D G J M E C B F K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        (inv_main54 J I O N H E G K B A D M F L P)
        (and (= C 1) (not (= F 0)))
      )
      (inv_main57 J I O N H E G K B A D M F C P)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (inv_main54 I M A L H O F B K J N E D C G)
        (= D 0)
      )
      (inv_main57 I M A L H O F B K J N E D C G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (inv_main57 C I B F E M O D H K N L J G A)
        (= C 0)
      )
      (inv_main60 C I B F E M O D H K N L J G A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        (inv_main57 L M B N C F O E P A D G I K J)
        (and (not (= L 0)) (= H 0) (= M 1))
      )
      (inv_main60 L H B N C F O E P A D G I K J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (inv_main60 D N O E B M L J G K A C H F I)
        (= O 0)
      )
      (inv_main66 D N O E B M L J G K A C H F I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        (inv_main60 E G A J K N B H D O I M F L C)
        (and (= P 0) (= J 1) (not (= A 0)))
      )
      (inv_main66 E G A P K N B H D O I M F L C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (inv_main78 F E N O M B I J G A L H C D K)
        (= G 0)
      )
      (inv_main84 F E N O M B I J G A L H C D K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        (inv_main78 H A C G L M E F O P N J K B I)
        (and (not (= O 0)) (= D 0) (= P 1))
      )
      (inv_main84 H A C G L M E F O D N J K B I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (inv_main84 G K I F D E A N J C H L O M B)
        (= H 0)
      )
      (inv_main90 G K I F D E A N J C H L O M B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        (inv_main84 P I A N D E L G F O M H K B C)
        (and (= J 0) (= H 1) (not (= M 0)))
      )
      (inv_main90 P I A N D E L G F O M J K B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) ) 
    (=>
      (and
        (inv_main42 I E F K A D L Q J M G P C O N)
        (and (= B 1) (not (= L 0)) (= H 1) (not (= A 0)))
      )
      (inv_main48 I E F K A B L H J M G P C O N)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        (inv_main42 H J B P N C O L D F M A I K G)
        (and (not (= N 0)) (= E 1) (= O 0))
      )
      (inv_main48 H J B P N E O L D F M A I K G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        (inv_main42 D O C A E L K M I P G J H N F)
        (and (= E 0) (= B 1) (not (= K 0)))
      )
      (inv_main48 D O C A E L K B I P G J H N F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (inv_main42 C D K F H I M O E G A J L N B)
        (and (= H 0) (= M 0))
      )
      (inv_main48 C D K F H I M O E G A J L N B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) ) 
    (=>
      (and
        (inv_main24 U E R O W B V N S G C A D Q P)
        (and (= H 0)
     (not (= U 0))
     (not (= T 0))
     (not (= R 0))
     (= M 0)
     (= L 1)
     (= K 1)
     (= J 0)
     (= I 0)
     (= F 0))
      )
      (inv_main42 U L R K W H V J S M C I D F T)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) ) 
    (=>
      (and
        (inv_main24 R D U B T I N F W M A H E S C)
        (and (= V 0)
     (= U 0)
     (not (= R 0))
     (= Q 0)
     (= P 0)
     (= O 0)
     (= L 0)
     (= K 0)
     (not (= J 0))
     (= G 1))
      )
      (inv_main42 R G U Q T V N L W O A K E P J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) ) 
    (=>
      (and
        (inv_main24 N D S W R E C Q B P G O K V L)
        (and (= A 1)
     (= H 0)
     (= U 0)
     (= T 0)
     (not (= S 0))
     (= N 0)
     (= M 0)
     (= J 0)
     (not (= I 0))
     (= F 0))
      )
      (inv_main42 N T S A R F C H B U G M K J I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) ) 
    (=>
      (and
        (inv_main24 S E F O R C K B T D H N W Q J)
        (and (= A 0)
     (= G 0)
     (= V 0)
     (= U 0)
     (= S 0)
     (= P 0)
     (= M 0)
     (not (= L 0))
     (= I 0)
     (= F 0))
      )
      (inv_main42 S A F M R V K P T U H G W I L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (inv_main72 O H L G A J F B I D M K C E N)
        (= F 0)
      )
      (inv_main78 O H L G A J F B I D M K C E N)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        (inv_main72 J C B E A H K O D N G I F P M)
        (and (= L 0) (not (= K 0)) (= O 1))
      )
      (inv_main78 J C B E A H K L D N G I F P M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (inv_main57 H A N D O I F L C E J B K G M)
        (and (not (= A 1)) (not (= H 0)))
      )
      (inv_main101 H A N D O I F L C E J B K G M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (inv_main60 N K J L F H E M C O A G B D I)
        (and (not (= J 0)) (not (= L 1)))
      )
      (inv_main101 N K J L F H E M C O A G B D I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (inv_main66 A N I O M F K H C L G E B J D)
        (and (not (= F 1)) (not (= M 0)))
      )
      (inv_main101 A N I O M F K H C L G E B J D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (inv_main72 E D F I O K M C N A J H G B L)
        (and (not (= C 1)) (not (= M 0)))
      )
      (inv_main101 E D F I O K M C N A J H G B L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (inv_main78 H D J F B O L A N I E G C M K)
        (and (not (= I 1)) (not (= N 0)))
      )
      (inv_main101 H D J F B O L A N I E G C M K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (inv_main84 B K O N F E G I D M L J H C A)
        (and (not (= J 1)) (not (= L 0)))
      )
      (inv_main101 B K O N F E G I D M L J H C A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (inv_main90 O C B L G M D A F N H K I E J)
        (and (not (= E 1)) (not (= I 0)))
      )
      (inv_main101 O C B L G M D A F N H K I E J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) ) 
    (=>
      (and
        (inv_main48 O C E H I A M B N P F D J Q G)
        (and (= L 1) (= K 1) (not (= F 0)) (not (= N 0)))
      )
      (inv_main54 O C E H I A M B N K F L J Q G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        (inv_main48 A H I B N F P L J D O K G E C)
        (and (= M 1) (not (= J 0)) (= O 0))
      )
      (inv_main54 A H I B N F P L J M O K G E C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) ) 
    (=>
      (and
        (inv_main48 J C I P G E D K O F N M H L B)
        (and (= O 0) (not (= N 0)) (= A 1))
      )
      (inv_main54 J C I P G E D K O F N A H L B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (inv_main48 B F H L G O C K D E J M N I A)
        (and (= D 0) (= J 0))
      )
      (inv_main54 B F H L G O C K D E J M N I A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) ) 
    (=>
      (and
        (inv_main101 J N L B I H A G O D K E C F M)
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
