import Props2Theories.TacticNames
-- Tactics (Rules) for Propositional Logic

-- 1) Straightforward tactics

example (p q : Prop) (h : p) (_ : q) : p := by
  exact h

example (p q : Prop) (h : p) (_ : q) : p := by
  apply h

example (p : Prop) (h : p) : p := by
  assumption

example (p : Prop) (h : p) : p := by
  try intro
  try intro_and
  try assumption



-- 2) True/False tactics

example : True := by
  intro_true

example : True := by
  _intro_true h
  assumption

example (p : Prop) (h : False) : p := by
  elim_false
  assumption

example (p : Prop) (h : False) : p := by
  elim_false_


-- 3) Implication tactics

example (p q : Prop) (h_pq : p → q) (h_p : p) : q := by
  apply h_pq
  assumption

example (p q : Prop) (h_pq : p → q) (h_p : p) : q := by
  specialize h_pq h_p
  assumption

example (p q : Prop) (h_pq : p → q) (h_p : p) : q := by
  exact (h_pq h_p)

example (p q : Prop) (h_pq : p → q) (h_p : p) : q := by
  revert h_p
  assumption

example (p q : Prop) (h_pq : p -> q) : p → q := by
  intro h_p
  specialize h_pq h_p
  assumption


-- 4) Subtheorem tactics

example (p q r: Prop) (hp : p) (hpq : p → q) (hqr : q → r) : r := by
  have hq : q := by
    exact hpq hp
  exact hqr hq

example (p q r: Prop) (hp : p) (hpq : p → q) (hqr : q → r) : r := by
  have hq : q := hpq hp
  exact hqr hq

example (p q r: Prop) (hp : p) (hpq : p → q) (hqr : q → r) : r := by
  let hq : q := hpq hp
  exact hqr hq

example (p q r: Prop) (hp : p) (hpq : p → q) (hqr : q → r) : r := by
  suffices hq : q by
    apply hqr
    exact hq
  exact hpq hp

example (p : Prop) (h : p) : p := by
  let h₂ := h
  clear h₂
  exact h


-- 5) Application by name

theorem some_name (p q : Prop) (h_pq : p → q) : p → q := by
  intro h_p
  let h_q := h_pq h_p
  assumption

example (p q : Prop) (h_pq : p -> q) : p → q := by
  exact (some_name p q h_pq)

example (p q : Prop) (h_pq : p -> q) : p → q := by
  apply (some_name p q h_pq)


-- 6) Tactic Flow

example (p q t : Prop) (h_pqt : p → q → t) : p → q → t := by
  intros h_p h_q
  apply h_pqt
  {
    assumption
  }
  {
    assumption
  }

example (p q t : Prop) (h_pqt : p → q → t) : p → q → t := by
  repeat (intro)
  apply h_pqt
  · assumption
  · assumption

example (p q t : Prop) (h_pqt : p → q → t) : p → q → t := by
  repeat (intro)
  apply h_pqt
  repeat (assumption)

example (p q t : Prop) (h_pqt : p → q → t) : p → q → t := by
  repeat (intro)
  apply h_pqt <;> assumption


-- 7) Conjunction rules

example (p q : Prop) (h_p : p) (h_q : q) : p ∧ q := by
  intro_and <;> assumption

example (p q : Prop) (h_p : p) (h_q : q) : p ∧ q := by
  intro_and_ h_p, h_q

example (p q : Prop) (h_p : p) (h_q : q) : p ∧ q := by
  _intro_and h_p, h_q, h_new
  assumption

example (p q : Prop) (h_pq : p ∧ q) : p := by
  elim_and h_pq, h_p, h_q
  assumption

example (p q : Prop) (h_pq : p ∧ q) : q := by
  elim_and h_pq, h_p, h_q
  assumption

example (p q : Prop) (h_pq : p ∧ q) : p := by
  elim_andc h_pq, h_p, h_q
  assumption

example (p q : Prop) (h_pq : p ∧ q) : p := by
  elim_and_ h_pq

example (p q : Prop) (h_pq : p ∧ q) : q := by
  elim_and_ h_pq

-- 8) Disjunction rules

example (p q : Prop) (h_p : p) : p ∨ q := by
  left
  assumption

example (p q : Prop) (h_p : q) : p ∨ q := by
  right
  assumption

example (p q : Prop) (h_p : p) : p ∨ q := by
  left_

example (p q : Prop) (h_q : q) : p ∨ q := by
  right_

example (p q : Prop) (h_p : p) : p ∨ q := by
  _left h_p , q , h_pq
  assumption

example (p q : Prop) (h_q : q) : p ∨ q := by
  _right h_q, p, h_pq
  assumption

example (p q r : Prop) (h_pq : p ∨ q) (h_pr : p → r) (h_qr : q → r) : r := by
  elim_or h_pq, h_p, h_q
  · exact h_pr h_p
  · exact h_qr h_q

example (p q r : Prop) (h_pq : p ∨ q) (h_pr : p → r) (h_qr : q → r) : r := by
  elim_or_ h_pq, h_pr, h_qr

example (p q r : Prop) (h_pq : p ∨ q) (h_pr : p → r) (h_qr : q → r) : r := by
  _elim_or h_pq, r, h_new
  apply h_new <;> assumption

example (p q r : Prop) (h_pq : p ∨ q) (h_pr : p → r) (h_qr : q → r) : r := by
  _elim_or_app h_pq, h_pr, h_qr, h_r
  assumption


-- 9) Logical Equivalence rules

example (p q : Prop) (h_pq : p → q) (h_qp : q → p) : p ↔ q := by
  intro_iff <;> assumption

example (p q : Prop) (h_pq : p → q) (h_qp : q → p) : p ↔ q := by
  intro_iff_ h_pq, h_qp

example (p q : Prop) (h_pq : p → q) (h_qp : q → p) : p ↔ q := by
  _intro_iff h_pq, h_qp, h_p_iff_q
  assumption

example (p q : Prop) (h_piq : p ↔ q) : p → q := by
  elim_iff h_piq, h_pq, h_qp
  assumption

example (p q : Prop) (h_piq : p ↔ q) : q → p := by
  elim_iff h_piq, h_pq, h_qp
  assumption

example (p q : Prop) (h_piq : p ↔ q) : p → q := by
  elim_iff_ h_piq

example (p q : Prop) (h_piq : p ↔ q) : q → p := by
  elim_iff_ h_piq

example (p q : Prop) (h_piq : p ↔ q) (h_p : p) : q := by
  apply_l h_piq
  assumption

example (p q : Prop) (h_piq : p ↔ q) (h_q : q) : p := by
  apply_r h_piq
  assumption

example (p q : Prop) (h_piq : p ↔ q) (h_p : p) : q := by
  apply_l_ h_piq

example (p q : Prop) (h_piq : p ↔ q) (h_q : q) : p := by
  apply_r_ h_piq

example (p q : Prop) (h_piq : p ↔ q) (h_p : p) : q := by
  _apply_l h_piq, h_p, h_q
  assumption

example (p q : Prop) (h_piq : p ↔ q) (h_q : q) : p := by
  _apply_r h_piq, h_q, h_p
  assumption

example (p q : Prop) (h_piq : p ↔ q) (h_p : p) : q := by
  _apply_lc h_piq, h_p, h_q
  assumption

example (p q : Prop) (h_piq : p ↔ q) (h_q : q) : p := by
  _apply_rc h_piq, h_q, h_p
  assumption


-- 10) Negation rules

example (p : Prop) (h_pF : p → False) : ¬p := by
  intro_neg h_p
  apply h_pF
  assumption

example (p : Prop) (h_pF : p → False) : ¬p := by
  intro_neg_

example (p : Prop) (h_pF : p → False) : ¬p := by
  _intro_neg h_pF, h_np
  assumption

example (p : Prop) (h_p : p) (h_np : ¬p) : False := by
  elim_neg h_np
  assumption

example (p : Prop) (h_p : p) (h_np : ¬p) : False := by
  elim_neg_ h_np

example (p : Prop) (h_p : p) (h_np : ¬p) : False := by
  _elim_neg h_np, h_pF
  exact (h_pF h_p)

example (p : Prop) (h_p : p) (h_np : ¬p) : False := by
  _elim_neg_app h_p, h_np, hf
  assumption

example (p q : Prop) (h_p : p) (h_np : ¬p) : q := by
  elim_false
  elim_neg_ h_np

example (p q : Prop) (h_p : p) (h_np : ¬p) : q := by
  elim_f_neg h_np

example (p q : Prop) (h_p : p) (h_np : ¬ p) : q := by
  _elim_f_neg h_np, q, h_q
  assumption

-- 11) Classical By Contradiction Rules


example (p : Prop) (h_npF : ¬p → False) : p := by
  by_contra_cl h_np
  exact (h_npF h_np)

example (p : Prop) (h_npF : ¬p → False) : p := by
  by_contra_cl_

example (p : Prop) (h_npF : ¬p → False) : p := by
  _by_contra_cl h_npF, h_p
  assumption


-- 12) Instance inferring

-- another way to prove something having tedious long,
-- but simple and straightforward on each step
-- is through instance inferring techinque
-- for example:

-- this means a structure with statements (here with one statement: eqv)

lemma neg_congr (p q : Prop) : (p ↔ q) → (¬p ↔ ¬q) := sorry
lemma disj_congr_r (p q r : Prop) : (p ↔ q) → ((p ∨ r) ↔ (q ∨ r)) := sorry
lemma conj_congr_r (p q r : Prop) : (p ↔ q) → ((p ∧ r) ↔ (q ∧ r)) := sorry
lemma disj_congr_l (p q r : Prop) : (p ↔ q) → ((r ∨ p) ↔ (r ∨ q)) := sorry
lemma conj_congr_l (p q r : Prop) : (p ↔ q) → ((r ∧ p) ↔ (r ∧ q)) := sorry
lemma impl_congr_right (p q r : Prop) : (p ↔ q) → ((p → r) ↔ (q → r)) := sorry
lemma impl_congr_left (p q r : Prop) : (p ↔ q) → ((r → p) ↔ (r → q)) := sorry
lemma iff_congr_right (p q r : Prop) : (p ↔ q) → ((p ↔ r) ↔ (q ↔ r)) := sorry
lemma iff_congr_left (p q r : Prop) : (p ↔ q) → ((r ↔ p) ↔ (r ↔ q)) := sorry

-- at first, it looks like I am thinking
example (p q r s : Prop) (h : p ↔ q) : ((¬p ∨ r) → s) ↔ ((¬q ∨ r) → s) := by
  apply impl_congr_right
  apply disj_congr_r
  apply neg_congr
  assumption

-- it can be done with a stupid algorithm
example (p q r s : Prop) (h : p ↔ q) : ((¬p ∨ r) → s) ↔ ((¬q ∨ r) → s) := by
  try assumption
  try apply neg_congr
  try apply disj_congr_r
  try apply conj_congr_r
  try apply disj_congr_l
  try apply conj_congr_r
  try apply impl_congr_right

  try assumption
  try apply neg_congr
  try apply disj_congr_r

  try assumption
  try apply neg_congr

  try assumption




class MyIff (P Q : Prop) : Prop where
  eqv : P ↔ Q

instance neg_congr_inst (p q : Prop) [hpq : MyIff p q] :
    MyIff (¬p) (¬q) := ⟨ by
        apply neg_congr
        exact hpq.eqv
    ⟩


instance and_left_congr_inst (p : Prop) (q s : Prop) [hqs : MyIff q s] :
    MyIff (p ∧ q) (p ∧ s) := ⟨ by
        apply conj_congr_l
        exact hqs.eqv
    ⟩

instance and_right_congr_inst (p s : Prop) (q : Prop) [hps : MyIff p s] :
    MyIff (p ∧ q) (s ∧ q) := ⟨by
        apply conj_congr_r
        exact hps.eqv
    ⟩

instance or_left_congr_inst (p : Prop) (q s : Prop) [hqs : MyIff q s] :
    MyIff (p ∨ q) (p ∨ s) := ⟨ by
        apply disj_congr_l
        exact hqs.eqv
  ⟩

instance or_right_congr_inst (p s : Prop) (q : Prop) [hps : MyIff p s] :
    MyIff (p ∨ q) (s ∨ q) := ⟨by
        apply disj_congr_r
        exact hps.eqv
  ⟩


instance impl_left_congr_inst (p : Prop) (q s : Prop) [hqs : MyIff q s] :
    MyIff (p → q) (p → s) := ⟨ by
        apply impl_congr_left
        exact hqs.eqv
  ⟩

instance impl_right_congr_inst (p s : Prop) (q : Prop) [hps : MyIff p s] :
    MyIff (p → q) (s → q) := ⟨by
        apply impl_congr_right
        exact hps.eqv
  ⟩

instance iff_left_congr_inst (p : Prop) (q s : Prop) [hqs : MyIff q s] :
    MyIff (p ↔ q) (p ↔ s) := ⟨by
        apply iff_congr_left
        exact hqs.eqv
  ⟩

instance iff_right_congr_inst (p s : Prop) (q : Prop) [hps : MyIff p s] :
    MyIff (p ↔ q) (s ↔ q) := ⟨by
        apply iff_congr_right
        exact hps.eqv
  ⟩


example (p q r s : Prop) (h : p ↔ q) : ((¬p ∨ r) → s) ↔ ((¬q ∨ r) → s) := by
  have h₂ : MyIff p q := ⟨by exact h⟩
  have h₃ : MyIff ((¬p ∨ r) → s) ((¬q ∨ r) → s) := by
    infer_instance
  exact h₃.eqv


-- 12) Equivalence Rewriting

axiom P (st : Prop) : Prop
axiom Q (st : Prop) : Prop
axiom S (st : Prop) : Prop

example (p q : Prop) (hiff : p ↔ q) (hpq : P q) : P p := by
  rewrite [hiff]
  assumption

example (p q : Prop) (hiff : p ↔ q) (hpp : P p) : P q := by
  rewrite [← hiff]
  assumption

example (p q : Prop) (hiff : p ↔ q) (hpp : P p) : P q := by
  rewrite [hiff] at hpp
  assumption

example (p q : Prop) (hiff : p ↔ q) (hpq : P q) : P p := by
  rewrite [← hiff] at hpq
  assumption

example (p q : Prop) (hiff : p ↔ q) (hpp : P p) (hqp : Q p) : P q ∧ Q q := by
  rewrite [hiff] at hqp
  rewrite [hiff] at hpp
  intro_and_ hpp, hqp


example (p q : Prop) (hiff : p ↔ q) (hpp : P p) (hqp : Q p) : P q ∧ Q q := by
  rewrite [hiff] at *
  intro_and_ hpp, hqp

example  (p q : Prop) (hiff : p ↔ q) (hpq : P q) (hqq : Q q) : P p ∧ Q p := by
  rewrite [hiff] at ⊢
  intro_and_ hpq, hqq


example (p q : Prop) (hiff : p ↔ q) (hpq : P q) (hqq : Q p) : P p ∧ Q p := by
  conv =>
    lhs
    rewrite [hiff]
  intro_and_ hpq, hqq

example (p q : Prop) (hiff : p ↔ q) (hpq : P q) (hqq : Q p) : Q p ∧ P p := by
  conv =>
    rhs
    rewrite [hiff]
  intro_and_ hqq, hpq

example (p q : Prop) (hiff : p ↔ q) (hpq : P q) (hqq : Q p) : P p ∧ Q p := by
  conv =>
    arg 1
    rewrite [hiff]
  intro_and_ hpq, hqq

example (p q : Prop) (hiff : p ↔ q) (hpq : P q) (hqq : Q p) : Q p ∧ P p := by
  conv =>
    arg 2
    rewrite [hiff]
  intro_and_ hqq, hpq

example (p q : Prop) (hiff : p ↔ q) (hpq : P q ∧ S q) (hqq : Q p) : P p ∧ Q p ∧ S q := by
  conv at hpq =>
    arg 1
    rewrite [← hiff]
  elim_and hpq, h_Pp, h_Sq
  intro_and
  assumption
  intro_and <;> assumption


example (p q : Prop) (hiff : p ↔ q) (hpq : P q) (hqq : Q q) : P p ∧ Q p := by
  rewrite [←hiff] at hpq hqq
  intro_and_ hpq, hqq

example (p q : Prop) (hiff : p ↔ q) (hpp : P p) (hqp : Q p) : P q ∧ Q q := by
  rewrite [hiff] at hpp hqp
  intro_and_ hpp, hqp

example (p q : Prop) (hiff : p ↔ q) (hpq : P q) (hqq : Q q) (_ : q) : P q ∧ Q q := by
  rewrite [←hiff] at hpq hqq ⊢
  intro_and_ hpq, hqq


-- 13) rw

lemma trivial_equivalence (p : Prop) : p ↔ p := sorry

example (p q : Prop) (hiff : p ↔ q) : P p ↔ P q := by
  rewrite [hiff]
  apply trivial_equivalence

-- LEAN 4 knows
-- You can't use rw before proving that iff is reflexive (trivial_equivalence)!

example (p q : Prop) (hiff : p ↔ q) : P p ↔ P q := by
  rw [hiff]


-- 14) calc structure

-- When you already proved the transitivity:

theorem iff_transitivity (p q r : Prop) : (p ↔ q) → (q ↔ r) → (p ↔ r) := sorry


example (p q r s : Prop) (hpq : p ↔ q) (hqr : q ↔ r) (hrs : r ↔ s) : p ↔ s := by
  apply iff_transitivity p r s <;> try assumption
  apply iff_transitivity p q r <;> assumption


-- you can use calc tactic
-- Which looks more elegant

def R (p q : Prop) : Prop := p ↔ q

instance : Trans R R R where
  trans := @iff_transitivity

example (p q r s : Prop) (hpq : p ↔ q) (hqr : q ↔ r) (hrs : r ↔ s) : p ↔ s := by
  calc
    R p q := hpq
    R q r := hqr
    R r s := hrs

example (p q r s : Prop) (hpq : p ↔ q) (hqr : q ↔ r) (hrs : r ↔ s) : p ↔ s := by
  calc
    R p _ := hpq
    R _  r := hqr
    R _ s := hrs

example (p q r s : Prop) (hpq : p ↔ q) (hqr : q ↔ r) (hrs : r ↔ s) : p ↔ s := by
  calc
    R _ _ := hpq
    R _  r := hqr
    R _ _ := hrs

-- LEAN 4 knows, ↔ is transitive
-- You can't use calc before proving that iff is transitive (iff_transitivity)!
example (p q r s : Prop) (hpq : p ↔ q) (hqr : q ↔ r) (hrs : r ↔ s) : p ↔ s := by
  calc
    _ ↔ _ := hpq
    _  ↔ r := hqr
    _ ↔ _ := hrs
