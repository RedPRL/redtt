type name = string

type 'a f = 
| Unit
| Bool
| Pi of 'a * name * 'a
| Sg of 'a * name * 'a
| Eq of name * 'a * 'a * 'a
| Lam of name * 'a
| Pair of 'a * 'a
| Ax 
| Tt
| Ff
| Dim0
| Dim1
| U of int
| Var of name
| App of 'a * 'a 
| Proj1 of 'a
| Proj2 of 'a
| If of name * 'a * 'a * 'a * 'a
| Of of 'a * 'a

type 'a t = Node of {info : 'a; con : 'a t f}