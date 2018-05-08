type tactic = unit ElabMonad.m
type name = string option

exception NotApplicable

module Pi :
sig
  val formation : name -> tactic
  val intro : name -> tactic
end

module Sg :
sig
  val formation : name -> tactic
  val intro : tactic
end

val under : tactic -> tactic
