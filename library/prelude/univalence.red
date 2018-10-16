import prelude.path
import prelude.connection
import prelude.hlevel
import prelude.equivalence

def ua (A B : type) (E : equiv A B) : path^1 type A B =
  λ i →
    `(V i A B E)

def ua/proj (A B : type) (E : equiv A B)
  : pathd (λ i → `(V i A B E) → B) (λ a → E.fst a) (λ b → b)
  =
  λ i u →
    `(vproj i u (fst E))

def univalence (B : type) : is-contr^1 ((A : type) × equiv A B) =
  ( (B, id-equiv/weak-connection B)
  , λ w i →
      let VB : type = `(V i (fst w) B (snd w)) in
      let proj/B (g : VB) : B = `(vproj i g (fst (snd w))) in
      ( _
      , proj/B
      , λ b →
        let ctr/B (j : 𝕀) : B =
          comp 1 j b [
          | i=0 → w.snd.snd b .fst .snd
          | i=1 → refl
          ]
        in
        let ctr : fiber VB B proj/B b =
          (`(vin i (fst (fst ((snd (snd w)) b))) (@ ctr/B 0)), ctr/B)
        in
        ( ctr
        , λ v j →
          let filler (l : 𝕀) : B =
            comp 1 l b [
            | i=0 → w.snd.snd b .snd v j .snd
            | i=1 k → weak-connection/or B (v.snd) j k
            | j=0 → v.snd
            | j=1 → ctr/B
            ]
          in
          ( `(vin i (fst (@ ((snd ((snd (snd w)) b)) v) j)) (@ filler 0))
          , filler
          )
        )
      )
  )
