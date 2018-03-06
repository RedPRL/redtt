type t
val define : ctx:t -> ty:Val.d -> tm:Val.d -> t
val add : ctx:t -> ty:Val.d -> t * Val.d

val env : ctx:t -> Val.env
val tys : ctx:t -> Val.env
val len : ctx:t -> int