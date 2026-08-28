import Props2Theories.TacticNames

#check Prop


#check True
#check False

#check (¬True)
#check (True ∨ False)
#check (False ∧ True)
#check (False -> True)
#check (True ↔ False)

variable (p : Prop)
variable (q : Prop)
#check p
#check q


/-- error: Unknown constant `p`
-/
#guard_msgs in
#print p


variable (F : Type)
variable (obj : F)

/-- error: Unknown constant `F`
-/
#guard_msgs in
#print F

/-- error: Unknown constant `obj`
-/
#guard_msgs in
#print obj


def Prop2 := Prop

#check Prop2
#print Prop2

def Prop3 : Type := Prop

#check Prop3
#print Prop3


def some_definition (v n r : Prop) := (v ∨ n) ∧ r

#check some_definition
#check (some_definition True False False)
#print some_definition

def some_definition_2 := some_definition True False True

#check some_definition_2
#print some_definition_2

def some_definition_3 := (True ∨ False) ∧ True

#check some_definition_3
#print some_definition_3


theorem some_theorem : True := True.intro
theorem another_theorem (p : Prop) : False → p := fun (h : False) => False.elim h

#check some_theorem
#check another_theorem

#print some_theorem
#print another_theorem


theorem some_theorem₂ : True := by
  intro_true

theorem another_theorem₂ (p : Prop) : False → p := by
  intro hF
  elim_false_

#check some_theorem₂
#check another_theorem

#print some_theorem₂
#print another_theorem₂

lemma some_lemma : True := by
  intro_true

lemma another_lemma (p : Prop) : False → p := by
  intro hF
  elim_false_


#check some_lemma
#check another_lemma

#print some_lemma
#print another_lemma


example : True := by
  intro_true

example (p : Prop) : False → p := by
  intro hF
  elim_false_



lemma lemma_dont_know_how_to_prove (p : Prop) : p → p := sorry
theorem theorem_dont_know_how_to_prove (p : Prop)  : p → p := sorry
example (p : Prop)  : p → p := sorry

lemma lemma_dont_know_how_to_prove₂ (p : Prop)  : p → p := by
  admit
theorem theorem_dont_know_how_to_prove₂ (p : Prop)  : p → p := by
  admit
example (p : Prop)  : p → p := by
  admit


axiom my_axiom (p : Prop) : False → p

axiom very_strange : False
#check very_strange

axiom another_strange (p : Prop) : p

axiom p₂ : Prop
axiom q₂ : Prop
#check p₂
#check q₂

axiom F₂ : Type
axiom obj₂ : F₂


structure MyStructure (a b c : Prop) : Prop where
  some_statement : a ↔ b
  another_statement : ¬ c

theorem my_structure_instance : MyStructure True True False := ⟨
    by rw [],
    by intro h; assumption
  ⟩

theorem my_structure_instance₂ : MyStructure False False False := ⟨
    by rw [],
    by intro h; assumption
  ⟩

#check MyStructure
#print MyStructure


class MyClass (a b c : Prop) : Prop where
  some_statement : a ↔ b
  another_statement : ¬ c


#check MyClass
#print MyClass


instance my_class_instance₁ : MyClass True True False := ⟨
    by rw [],
    by intro h; assumption
  ⟩

instance my_class_instance₂ : MyClass False False False := ⟨
    by rw [],
    by intro h; assumption
  ⟩
