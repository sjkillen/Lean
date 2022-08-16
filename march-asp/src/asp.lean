constant Atom: Type

inductive TVal
  | t
  | u
  | f


structure Rule :=
  (head: Atom)
  (pbody: list Atom)
  (nbody: list Atom)


inductive RuleState
| applied
| unapplied
| discarded


structure Program' :=
  (i: list Atom × TVal)