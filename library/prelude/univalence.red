import prelude.path
import prelude.connection
import prelude.hlevel
import prelude.equivalence

def ua (A B : type) (e : equiv A B) : path^1 type A B =
  λ i → V i A B e

def univalence (B : type) : is-contr^1 ((A : type) × equiv A B) =
  ( (B, id-equiv B)
  , λ (A,e) i →
    let VB : type = V i A B e in
    let proj/B (g : VB) : B = g .vproj in
    ( _
    , proj/B
    , λ b →
      let ctr/B (j : 𝕀) : B =
        comp 1 j b [
        | i=0 → e .snd b .fst .snd
        | i=1 → refl
        ]
      in
      let ctr : fiber VB B proj/B b =
        ((e .snd b .fst .fst, ctr/B 0), ctr/B)
      in
      ( ctr
      , λ v j →
        let aux (k : 𝕀) : B =
          comp 1 k b [
          | j=0 → v .snd
          | j=1 → refl
          ]
        in
        let filler (l : 𝕀) : B =
          comp 1 l b [
          | i=0 → e .snd b .snd v j .snd
          | i=1 → aux
          | j=0 → v.snd
          | j=1 → ctr/B
          ]
        in
        -- MORTAL this should be: e .snd b .snd v j .fst
        ( `(vin i (fst (@ ((snd ((snd e) b)) v) j)) (@ filler 0))
        , filler
        )
      )
    )
  )
