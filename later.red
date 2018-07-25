import path

; to be able to program with this, I really need the dimension-indexed dfix.

let stream : type =
  `(prev ∙
    (dfix 0 (U 0) [A]
     (× bool (▷ [α] (prev α A)))))

debug
