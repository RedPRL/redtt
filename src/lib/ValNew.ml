module Tm = TmNew

type can = [`Can]
type neu = [`Neu]

type 'a bnd = B of 'a

type _ t = 
| Idx : int -> neu t
| Lvl : int -> neu t

| Up : can t * neu t -> can t

| Pi : clo * bclo -> can t
| Sg : clo * bclo -> can t
| Univ : Tm.Lvl.t -> can t

| Lam : bclo -> can t
| Cons : clo * clo -> can t

| Coe : can t * can t * can t bnd * can t -> can t

| App : neu t * can t -> neu t
| Car : neu t -> neu t
| Cdr : neu t -> neu t


and env = can t list
and clo = Clo of Thin.t0 * (Tm.chk Tm.t * env * Thin.t0)
and bclo = BClo of Thin.t0 * (Tm.chk Tm.t * env * Thin.t0)


