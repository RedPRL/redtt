; this file contains a direct proof of univalence
import equivalence
import connection
import connection

let IdEquiv/connection (B : type) : Equiv B B =
  < λ b → b
  , λ b →
    < <b, refl>
    , λ v i → <v.1 i, λ j → connection/or B (v.1) i j>
    >
  >

let univalence/alt (B : type) : IsContr^1 ((A : type) × Equiv A B) =
  < <B, IdEquiv/connection B>
  , λ w i →
      let VB : type = `(V i (fst w) B (snd w)) in
      let proj/B : VB → B = λ g → `(vproj i g (fst w) B (snd w)) in
      < _
      , proj/B
      , λ b →
           let ctr/B : dim → B =
             λ j →
               comp 1 j b [
               | i=0 ⇒ w .1 .1 b .0 .1
               | i=1 ⇒ refl
               ]
           in
           let ctr : Fiber VB B proj/B b =
             < `(vin i (fst (fst ((snd (snd w)) b))) (@ ctr/B 0)), ctr/B >
           in
           < ctr
           , λ v j →
               let filler : dim → B =
                 λ l →
                   comp 1 l b [
                   | i=0 ⇒ w .1 .1 b .1 v j .1
                   | i=1 ⇒ λ k → connection/or B (v .1) j k
                   | j=0 ⇒ v .1
                   | j=1 ⇒ ctr/B
                   ]
               in
               < `(vin i (fst (@ ((snd ((snd (snd w)) b)) v) j)) (@ filler 0))
               , filler
               >
           >
      >
  >


