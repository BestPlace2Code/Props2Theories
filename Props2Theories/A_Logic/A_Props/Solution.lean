import Props2Theories.TacticNames

-- True and False laws
theorem neg_true : ¬ True ↔ False:= sorry
theorem neg_false : ¬ False ↔ True := sorry
theorem conj_true (p : Prop) : p ∧ True ↔ p := sorry
theorem conj_false (p : Prop) : p ∧ False ↔ False := sorry
theorem disj_true (p : Prop) : p ∨ True ↔ True := sorry
theorem disj_false (p : Prop) : p ∨ False ↔ p := sorry
theorem impl_true (p : Prop) : (p → True) ↔ True := sorry
theorem true_impl (p : Prop) : (True → p) ↔ p := sorry
theorem impl_false (p : Prop) : (p → False) ↔ ¬ p := sorry
theorem false_impl (p : Prop) : (False → p) ↔ True := sorry

--Idempodent laws
theorem axiomatic_rule (p : Prop) : p → p := sorry
theorem trivial_equivalence (p : Prop) : p ↔ p := sorry
theorem conj_idemp (p : Prop) : p ↔ (p ∧ p) := sorry
theorem disj_idemp (p : Prop) : p ↔ (p ∨ p) := sorry

--Absorption laws
theorem absorbtion_disj (p q : Prop) : p ∨ (p ∧ q) ↔ p := sorry
theorem absorbtion_conj (p q : Prop) : p ∧ (p ∨ q) ↔ p := sorry

--Commutativity laws
theorem conj_symm (p q : Prop) : (p ∧ q) → (q ∧ p) := sorry
theorem conj_commut (p q : Prop) : (p ∧ q) ↔ (q ∧ p) := sorry
theorem disj_symm (p q : Prop) : (p ∨ q) → (q ∨ p) := sorry
theorem disj_commut (p q : Prop) : (p ∨ q) ↔ (q ∨ p) := sorry
theorem iff_symm (p q : Prop) : (p ↔ q) → (q ↔ p) := sorry
theorem iff_commut (p q : Prop) : (p ↔ q) ↔ (q ↔ p) := sorry

--Associativity laws
theorem conj_assoc (p q r : Prop) : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
theorem disj_assoc (p q r : Prop) : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

--Distributivity laws
theorem conj_disj_distrib (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
theorem disj_conj_distrib (p q r : Prop) : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

--Weak pierce law
--Dont' use classical rules
theorem weak_pierce_law (p q : Prop) : ((((p → q) → p) → p) → q) → q := sorry

--3 De Morgan Intuitionistic implications
--Don't use classic rules
theorem morgan_disj (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
theorem morgan_conj_rl (p q : Prop) : ¬p ∨ ¬q → ¬(p ∧ q) := sorry

--Implication and negative implication sufficiencies
theorem neg_to_impl (p q : Prop) : ¬p → (p → q)  := sorry
theorem impl_def_lr (p q : Prop) : (¬p ∨ q) → (p → q)  := sorry
theorem neg_imp_def_rl (p q : Prop) : p ∧ ¬q → ¬(p → q)  := sorry

-- Direct contraposition
theorem contraposition_lr (p q : Prop) : (p → q) → (¬q → ¬p) := sorry

-- Exportation (currying) law
theorem exportation_law (p q r : Prop) : (p → (q → r)) ↔ (p ∧ q → r) := sorry

-- Disjunction in implication antecedent
theorem cases_impl_left (p q r : Prop) : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry

-- Syllogism
theorem syllogism (p q r : Prop) : (p → q) → (q → r) → (p → r) := sorry

--Transitivity of equivalence
theorem iff_transitivity (p q r : Prop) : (p ↔ q) → (q ↔ r) → (p ↔ r) := sorry

--Congruence laws
theorem neg_congr (p q : Prop) : (p ↔ q) → (¬p ↔ ¬q) := sorry
theorem disj_congr_r (p q r : Prop) : (p ↔ q) → ((p ∨ r) ↔ (q ∨ r)) := sorry
theorem conj_congr_r (p q r : Prop) : (p ↔ q) → ((p ∧ r) ↔ (q ∧ r)) := sorry
theorem disj_congr_l (p q r : Prop) : (p ↔ q) → ((r ∨ p) ↔ (r ∨ q)) := sorry
theorem conj_congr_l (p q r : Prop) : (p ↔ q) → ((r ∧ p) ↔ (r ∧ q)) := sorry
theorem impl_congr_right (p q r : Prop) : (p ↔ q) → ((p → r) ↔ (q → r)) := sorry
theorem impl_congr_left (p q r : Prop) : (p ↔ q) → ((r → p) ↔ (r → q)) := sorry
theorem iff_congr_ (p q r : Prop) : (p ↔ q) → ((p ↔ r) ↔ (q ↔ r)) := sorry

--Equivalence to both conditions
theorem iff_conj_intro(p q r : Prop) : (p ↔ q) → (p ↔ r) → (p ↔ (q ∧ r)) := sorry

--Noncontradiction law
theorem no_contradiction (p : Prop) : ¬(p ∧ ¬ p) := sorry

--Direct double negation
theorem double_negation_lr (p : Prop) : p → ¬¬ p := sorry

--Nonequivalence of opposites
--Don't use classical rules
theorem negation_not_equiv (p : Prop) : ¬(p ↔ ¬p) := sorry

--Classical double negation
theorem double_negation_cl (p : Prop) : p ↔ ¬¬p := sorry

--Classical tertsium non datur (law of excluded middle)
theorem tnd_cl (p : Prop) : p ∨ ¬ p := sorry


--Classical cases rules
theorem cases_analysis_cl (p q : Prop) : (p → q) → (¬p → q) → q := sorry
theorem cases_analysis_l_cl (p q r : Prop) : (p ∨ q) → (p → r) → (q → (¬p → r)) → r := sorry
theorem cases_analysis_r_cl (p q r : Prop) : (p ∨ q) → (q → r) → (p → (¬q → r)) → r := sorry
theorem cases_impl_right_cl (p q r : Prop) : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry

--One of the De Morgan classical law
theorem morgan_conj_cl (p q : Prop) : ¬ (p ∧ q) ↔ ¬p ∨ ¬q := sorry

--Implication and neg implication classical equivalence
theorem impl_def_cl (p q : Prop) : (p → q) ↔ (¬p ∨ q) := sorry
theorem neg_imp_def_cl (p q : Prop) :  ¬ (p → q) ↔ p ∧ ¬ q := sorry

--Classical contraposition
theorem contraposition_cl (p q : Prop) : (p → q) ↔ (¬q → ¬p) := sorry

--Classical Pierce law
theorem pierce_cl (p q : Prop) : (((p → q) → p) → p) := sorry


--Associativity of Equivalence
theorem impl_assoc_cl (p q r : Prop) : (p ↔ (q ↔ r)) ↔ ((p ↔ q) ↔ r) := sorry

-- Xor Logical Operator Definition
def xor_pr (p q : Prop) : Prop := (p ∧ ¬q) ∨ (q ∧ ¬p)
notation:10 p " ⊕ " q:11 => xor_pr p q

-- Xor Simple Rules
theorem xor_introl (p q : Prop) : (p ∧ ¬q) → (p ⊕ q) := sorry
theorem xor_intror (p q : Prop) : (q ∧ ¬p) → (p ⊕ q) := sorry
theorem xor_intro (p q : Prop) : (p ∨ q) → (¬ (p ∧ q)) → (p ⊕ q) := sorry
theorem xor_left (p q : Prop) : (p ⊕ q) → (p ∨ q) := sorry
theorem xor_right (p q : Prop) : (p ⊕ q) → (¬ (p ∧ q)) := sorry
theorem xor_elim (p q r : Prop) : (p ⊕ q) → ((p ∧ ¬q) → r) → ((q ∧ ¬p) → r) → r := sorry

-- Xor Properties
theorem xor_equiv_def (p q : Prop) : (p ⊕ q) ↔ ((p ∨ q) ∧ (¬ (p ∧ q))) := sorry
theorem xor_not_iff_cl (p q : Prop) : (p ⊕ q) ↔ (¬ (p ↔ q)) := sorry
theorem iff_not_xor_cl (p q : Prop) : (p ↔ q) ↔ (¬ (p ⊕ q)) := sorry
theorem xor_equal (p : Prop) : ¬ (p ⊕ p) := sorry
theorem xor_neg (p : Prop) : (p ⊕ ¬ p) := sorry
theorem xor_commut (p q : Prop) : (p ⊕ q) ↔ (q ⊕ p) := sorry
theorem xor_assoc_cl (p q r : Prop) : ((p ⊕ q) ⊕ r) ↔ (p ⊕ (q ⊕ r)) := sorry
theorem xor_absorb_cl (p q : Prop) : q ↔ ((p ⊕ q) ⊕ p) := sorry
theorem xor_and_distr (p q r : Prop) : p ∧ (q ⊕ r) ↔ ((p ∧ q) ⊕ (p ∧ r)) := sorry
theorem xor_congr_l (p q r : Prop) : (p ↔ q) → ((p ⊕ r) ↔ (q ⊕ r)) := sorry
theorem xor_congr_r (p q r : Prop) : (p ↔ q) → ((r ⊕ p) ↔ (r ⊕ q)) := sorry
