def Atom := nat

structure Rule :=
  (head : list Atom)
  (pbody : list Atom)
  (nbody : list Atom)

structure ASPStructure :=
  (rules_off : list Rule)
  (rules_on : list Rule)
  (atoms_off : list Atom)
  (undef_on : list Atom)
  (truthy_on : list Atom)

section ASPStructure
  def rule_applicable (self : ASPStructure) (r : Rule) : Prop := sorry
end ASPStructure

structure Program :=
  (rules : list Rule)

section Program
  def struct (self : Program) : ASPStructure :=
    (ASPStructure.mk self.rules [] [] [] [])
end Program

inductive ASPOperator
| Program (p : Program)
| ApplyRule (p : ASPStructure) (r : Rule) (a : p.rule_applicable r)
| FalsifyAtoms

