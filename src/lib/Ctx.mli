type t
val emp : t

val define : ctx:t -> ty:Val.can Val.t -> tm:Val.can Val.t -> t
val add : ctx:t -> ty:Val.can Val.t -> t * Val.can Val.t

val len : ctx:t -> int