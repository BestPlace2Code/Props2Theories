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


-- 12) Equivalence Rewriting

example (P : Prop → Prop) (p q : Prop) (hiff : p ↔ q) (hpq : P q) : P p := by
  rewrite [hiff]
  assumption

example (P : Prop → Prop) (p q : Prop) (hiff : p ↔ q) (hpp : P p) : P q := by
  rewrite [← hiff]
  assumption

example (P : Prop → Prop) (p q : Prop) (hiff : p ↔ q) (hpp : P p) : P q := by
  rewrite [hiff] at hpp
  assumption

example (P : Prop → Prop) (p q : Prop) (hiff : p ↔ q) (hpq : P q) : P p := by
  rewrite [← hiff] at hpq
  assumption

example (P Q : Prop → Prop) (p q : Prop) (hiff : p ↔ q) (hpp : P p) (hqp : Q p) : P q ∧ Q q := by
  rewrite [hiff] at hqp
  rewrite [hiff] at hpp
  intro_and_ hpp, hqp


example (P Q : Prop → Prop) (p q : Prop) (hiff : p ↔ q) (hpp : P p) (hqp : Q p) : P q ∧ Q q := by
  rewrite [hiff] at *
  intro_and_ hpp, hqp

example  (P Q : Prop → Prop) (p q : Prop) (hiff : p ↔ q) (hpq : P q) (hqq : Q q) : P p ∧ Q p := by
  rewrite [hiff] at ⊢
  intro_and_ hpq, hqq


example (P Q : Prop → Prop) (p q : Prop) (hiff : p ↔ q) (hpq : P q) (hqq : Q p) : P p ∧ Q p := by
  conv =>
    lhs
    rewrite [hiff]
  intro_and_ hpq, hqq

example (P Q : Prop → Prop) (p q : Prop) (hiff : p ↔ q) (hpq : P q) (hqq : Q p) : Q p ∧ P p := by
  conv =>
    rhs
    rewrite [hiff]
  intro_and_ hqq, hpq

example (P Q : Prop → Prop) (p q : Prop) (hiff : p ↔ q) (hpq : P q) (hqq : Q p) : P p ∧ Q p := by
  conv =>
    arg 1
    rewrite [hiff]
  intro_and_ hpq, hqq

example (P Q : Prop → Prop) (p q : Prop) (hiff : p ↔ q) (hpq : P q) (hqq : Q p) : Q p ∧ P p := by
  conv =>
    arg 2
    rewrite [hiff]
  intro_and_ hqq, hpq

example (P Q S : Prop → Prop) (p q : Prop) (hiff : p ↔ q) (hpq : P q ∧ S q) (hqq : Q p) : P p ∧ Q p ∧ S q := by
  conv at hpq =>
    arg 1
    rewrite [← hiff]
  elim_and hpq, h_Pp, h_Sq
  intro_and
  assumption
  intro_and <;> assumption


example (P Q : Prop → Prop) (p q : Prop) (hiff : p ↔ q) (hpq : P q) (hqq : Q q) : P p ∧ Q p := by
  rewrite [←hiff] at hpq hqq
  intro_and_ hpq, hqq

example (P Q : Prop → Prop) (p q : Prop) (hiff : p ↔ q) (hpp : P p) (hqp : Q p) : P q ∧ Q q := by
  rewrite [hiff] at hpp hqp
  intro_and_ hpp, hqp

example (P Q : Prop → Prop) (p q : Prop) (hiff : p ↔ q) (hpq : P q) (hqq : Q q) (_ : q) : P q ∧ Q q := by
  rewrite [←hiff] at hpq hqq ⊢
  intro_and_ hpq, hqq


-- 13) rw

-- You can't use rw before proving that iff is reflexive (trivial_equivalence)!

example (P: Prop → Prop) (p q : Prop) (h_tri : P q ↔ P q) (hiff : p ↔ q) : P p ↔ P q := by
  rewrite [hiff]
  exact h_tri

example (P: Prop → Prop) (p q : Prop) (hiff : p ↔ q) : P p ↔ P q := by
  rw [hiff]


-- 14) calc structure

-- You can't use calc before proving that iff is transitive (iff_transitivity)!

-- When you already proved it:
-- Instead of using transitivity explicitly
example (p q r s : Prop) (h₁ : (p ↔ r) → (r ↔ s) → (p ↔ s)) (h₂ : (p ↔ q) → (q ↔ r) → (p ↔ r)) (hpq : p ↔ q) (hqr : q ↔ r) (hrs : r ↔ s) : p ↔ s := by
  apply h₁ <;> try assumption
  apply h₂ <;> assumption


-- you can use calc tactic
-- Which looks more elegant
example (p q r s : Prop) (hpq : p ↔ q) (hqr : q ↔ r) (hrs : r ↔ s) : p ↔ s := by
  calc
    p ↔ q := hpq
    q ↔ r := hqr
    r ↔ s := hrs

example (p q r s : Prop) (hpq : p ↔ q) (hqr : q ↔ r) (hrs : r ↔ s) : p ↔ s := by
  calc
    p ↔ q := hpq
    _ ↔ r := hqr
    _ ↔ s := hrs

example (p q r s : Prop) (hpq : p ↔ q) (hqr : q ↔ r) (hrs : r ↔ s) : p ↔ s := by
  calc
    _ ↔ q := hpq
    _ ↔ r := hqr
    _ ↔ _ := hrs
