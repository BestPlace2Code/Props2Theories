import Lean
open Lean Elab Tactic Meta PrettyPrinter
namespace Props2Theories




elab "intro_true" : tactic => do
  evalTactic (← `(tactic| exact True.intro))

elab "_intro_true" h:ident : tactic => do
  evalTactic (← `(tactic|
    have $h : True := trivial
  )
)

elab "elim_false" : tactic => do
  evalTactic  (← `(tactic| apply False.elim))

elab "elim_false_" : tactic => do
  evalTactic  (← `(tactic| apply False.elim; assumption))

elab "intro_and" : tactic => do
  evalTactic (← `(tactic| apply And.intro))

elab "intro_and_" hl:term "," hr:term : tactic => do
  evalTactic (← `(tactic| exact And.intro $hl $hr))

elab "_intro_and" hl:term "," hr:term "," h_new:ident : tactic => do (
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $h_new := And.intro $hl $hr
    )
  )
)

elab "elim_and" hlr:term "," hl:ident "," hr:ident : tactic => do
  evalTactic (← `(tactic|
    have $hl:ident := And.left $hlr;
    have $hr:ident := And.right $hlr;
  ))

elab "elim_andc" hlr:term "," hl:ident "," hr:ident : tactic => do
  evalTactic (← `(tactic|
    have $hl:ident := And.left $hlr;
    have $hr:ident := And.right $hlr;
    clear $hlr
  ))


elab "elim_and_" hlr:term : tactic => do
  evalTactic (← `(tactic|
    have _hl := And.left $hlr;
    have _hr := And.right $hlr;
    assumption
  ))

elab "left_" : tactic => do
  evalTactic (← `(tactic|
      left;
      assumption
    )
  )

elab "right_" : tactic => do
  evalTactic (← `(tactic|
      right;
      assumption
    )
  )


elab "_left" h_p:term "," q:term "," h_new:ident : tactic => do
  evalTactic (← `(tactic|
    have $h_new : _ ∨ $q := Or.inl $h_p
  ))


elab "_right" h_q:term "," p:term "," h_new:ident : tactic => do
  evalTactic (← `(tactic|
    have $h_new : $p ∨ _ := Or.inr $h_q
  ))

macro "elim_or" h_pq:term "," hl:ident "," hr:ident : tactic =>
  `(tactic|
    cases ($h_pq) with

    | inl $hl:ident => ?_
    | inr $hr:ident => ?_
  )

macro "elim_or_" h_pq:term "," f1:term "," f2:term : tactic =>
  `(tactic|
    cases ($h_pq) with

    | inl _h1 => exact $f1 _h1
    | inr _h2 => exact $f2 _h2
  )


elab "_elim_or" h:term "," r:term "," h_new:ident : tactic => do
  let h_expr ← elabTerm h none
  let h_type ← inferType h_expr

  let .app (.app (.const ``Or _) p) q := h_type.consumeMData

    | throwError "Гипотеза {h} не является дизъюнкцией (p ∨ q)"

  let p_stx ← delab p
  let q_stx ← delab q

  evalTactic (← `(tactic|
    have $h_new:ident : ($p_stx → $r) → ($q_stx → $r) → $r := by
      intros _hp_r _hq_r
      cases ($h) with

      | inl _hp => exact _hp_r _hp
      | inr _hq => exact _hq_r _hq
  ))


macro "_elim_or_app" h:term "," hpr:term "," hqr:term "," hr:ident : tactic =>
  `(tactic|
    -- We use 'match' to build the term directly.
    -- Lean is much better at inferring types from 'match' than from 'by cases'
    have $hr:ident :=
      match ($h) with

      | Or.inl hp => $hpr hp
      | Or.inr hq => $hqr hq
  )


elab "intro_iff" : tactic => do
  evalTactic (← `(tactic| apply Iff.intro))

elab "intro_iff_" hl:term "," hr:term : tactic => do
  evalTactic (← `(tactic| exact Iff.intro $hl $hr))

elab "_intro_iff" hl:term "," hr:term "," h_new:ident : tactic => do (
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $h_new := Iff.intro $hl $hr
    )
  )
)


elab "elim_iff" hlir:term "," hlr:ident "," hrl:ident : tactic => do
  evalTactic (← `(tactic|
    have $hlr:ident := Iff.mp $hlir;
    have $hrl:ident := Iff.mpr $hlir
  ))


elab "elim_iff_" hlir:term : tactic => do
  evalTactic (← `(tactic|
    have _hlr := Iff.mp $hlir;
    have _hrl := Iff.mpr $hlir;
    assumption
  ))

elab "apply_l" hlir:term : tactic => do
  evalTactic (← `(tactic|
    apply (Iff.mp $hlir);
  ))

elab "apply_r" hlir:term : tactic => do
  evalTactic (← `(tactic|
    apply (Iff.mpr $hlir);
  ))

elab "apply_l_" hlir:term : tactic => do
  evalTactic (← `(tactic|
    apply (Iff.mp $hlir);
    assumption
  ))

elab "apply_r_" hlir:term : tactic => do
  evalTactic (← `(tactic|
    apply (Iff.mpr $hlir);
    assumption
  ))

elab "_apply_l" hlir:term "," hl:term "," hr:ident : tactic => do
  evalTactic (← `(tactic|
    have $hr := (Iff.mp $hlir) ($hl);
  ))

elab "_apply_r" hlir:term "," hr:term "," hl:ident : tactic => do
  evalTactic (← `(tactic|
    have $hl := (Iff.mpr $hlir) ($hr);
  ))

elab "_apply_lc" hlir:term "," hl:term "," hr:ident : tactic => do
  evalTactic (← `(tactic|
    have $hr := (Iff.mp $hlir) ($hl);
    clear $hl
  ))

elab "_apply_rc" hlir:term "," hr:term "," hl:ident : tactic => do
  evalTactic (← `(tactic|
    have $hl := (Iff.mpr $hlir) ($hr);
    clear $hr
  ))

elab "intro_neg" h:ident : tactic => do
  evalTactic (← `(tactic|
    intro $h:ident
  ))

elab "intro_neg_" : tactic => do
  evalTactic (← `(tactic|
    assumption
  ))

elab "_intro_neg" h_pF:term "," h_np:ident : tactic => do
  evalTactic (← `(tactic|
    have $h_np : ¬ _ := $h_pF
  ))

elab "elim_neg" h_np:term : tactic => do
  evalTactic (← `(tactic|
    apply $h_np
  ))

elab "elim_neg_" h_np:term : tactic => do
  evalTactic (← `(tactic|
    apply $h_np;
    assumption
  ))

elab "_elim_neg" h_np:term "," h_pF:ident : tactic => do
  evalTactic (← `(tactic|
    have $h_pF : _ → False := $h_np
  ))

elab "_elim_neg_app" h_p:term "," h_np:term "," hf:ident : tactic => do
  evalTactic (← `(tactic|
    have $hf : False := $h_np $h_p
  ))

elab "elim_f_neg" h_np:term : tactic => do
  evalTactic (← `(tactic|
    apply (False.elim);
    elim_neg_ $h_np
  ))

elab "_elim_f_neg" h_np:term "," q:term "," h_q:ident : tactic => do
  evalTactic (← `(tactic|
    have $h_q : $q := by
      apply False.elim;
      elim_f_neg $h_np

  ))


axiom dneg_elim {p : Prop} (h_npF : ¬p → False) : p

elab "by_contra_cl" h_np:ident : tactic => do
  evalTactic (← `(tactic|
      apply dneg_elim;
      intro $h_np:ident;

  ))

elab "by_contra_cl_" : tactic => do
  evalTactic (← `(tactic|
      apply dneg_elim;
      assumption

  ))

elab "_by_contra_cl" h_npF:term "," h_p:ident : tactic => do
  evalTactic (← `(tactic|
      have $h_p := dneg_elim $h_npF
  ))


syntax "intro_exists" term : tactic
elab_rules : tactic

  | `(tactic| intro_exists $arg) => do
    evalTactic (← `(tactic|

    apply Exists.intro $arg


    ))


syntax "intro_exists_" term "," term : tactic
elab_rules : tactic

  | `(tactic| intro_exists_ $arg, $h) => do
    evalTactic (← `(tactic| apply Exists.intro $arg))
    evalTactic (← `(tactic| exact $h))

syntax "_intro_exists" term "," term "," ident : tactic
elab_rules : tactic

  | `(tactic| _intro_exists $arg, $h, $h_new) => do
    let hExpr ← elabTerm h none
    let argExpr ← elabTerm arg none

    let currentExpr ← mkAppM ``Exists.intro #[argExpr, hExpr]
    let type ← inferType currentExpr

    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.define h_new.getId type currentExpr
      let (_, mvarIdPost) ← mvarIdNew.intro1P
      return [mvarIdPost]


macro "elim_exists" h:term "," a:ident "," ha:ident : tactic =>
  `(tactic|
      let ⟨$a, $ha⟩ := $h
  )



elab "elim_existsc" h:term "," a:ident "," ha:ident : tactic => do
  evalTactic (← `(tactic|
     let ⟨$a, $ha⟩ := $h;
     clear $h
  ))



elab "elim_exists_" h:term "," hq:term : tactic => do
  evalTactic (← `(tactic|
     let ⟨_a, _Ha⟩ := $h;
      specialize ($hq _a);
      apply $hq;
      assumption
  ))




elab "_elim_exists" h:term "," Q:term "," newH:ident : tactic => do
  -- 1. Elaborate 'h' и получаем его тип
  let hExpr ← elabTerm h none
  let hType ← inferType hExpr

  let (fn, args) := hType.getAppFnArgs

  if fn == ``Exists && args.size == 2 then
    let pExpr := args[1]!
    let qExpr ← elabTerm Q none

    let predType ← inferType pExpr
    let xType := predType.bindingDomain!

    let innerForallExpr ← Meta.withLocalDecl `x BinderInfo.default xType fun x => do
      let pApp := mkApp pExpr x
      let pAppRed ← whnf pApp
      let pxQ ← mkArrow pAppRed qExpr
      mkForallFVars #[x] pxQ

    let fullTypeExpr ← mkArrow innerForallExpr qExpr

    let fullTypeSyntax ← delab fullTypeExpr

    evalTactic (← `(tactic|
       (have $newH : $fullTypeSyntax := by
          let ⟨_a, _Ha⟩ := $h
          intro _h_forq
          apply (_h_forq _a)
          exact _Ha
       )
    ))
  else
    throwError "Hypothesis {h} is not an existential (expected Exists P)."


elab "_elim_exists_app" h:term "," Q:term "," h_Q:term "," newH:ident : tactic => do
  let hExpr ← elabTerm h none
  let hType ← inferType hExpr

  let (fn, args) := hType.getAppFnArgs

  if fn == ``Exists && args.size == 2 then
    let pExpr := args[1]!
    let qExpr ← elabTerm Q none

    let predType ← inferType pExpr
    let xType := predType.bindingDomain!


    let innerForallExpr ← Meta.withLocalDecl `x BinderInfo.default xType fun x => do
      let pApp := mkApp pExpr x
      let pAppRed ← whnf pApp
      let pxQ ← mkArrow pAppRed qExpr
      mkForallFVars #[x] pxQ

    let fullTypeExpr ← mkArrow innerForallExpr qExpr

    let fullTypeSyntax ← delab fullTypeExpr

    evalTactic (← `(tactic|
       (have $newH : $fullTypeSyntax := by
          let ⟨_a, _Ha⟩ := $h
          intro _h_forq
          apply (_h_forq _a)
          exact _Ha
        specialize ($newH $h_Q)
       )
    ))
  else
    throwError "Hypothesis {h} is not an existential (expected Exists P)."



elab "_rfl" x:term "," h:ident : tactic => do
evalTactic (← `(tactic|
    have $h : $x = $x := by rfl
  ))

elab "propext_cl" h:term : tactic => do
  evalTactic (← `(tactic|
    apply propext;
    exact $h
  ))


elab "propext_cl_" : tactic => do
  evalTactic (← `(tactic|
    apply propext;
    assumption
  ))

elab "_propext_cl" h:term "," h_new:ident : tactic => do
  evalTactic (← `(tactic|
    have $h_new : _ = _ := propext $h
  ))


elab "_propext_cl_" : tactic => do
  evalTactic (← `(tactic|
    apply propext
  ))



elab "funext_cl" h:term : tactic => do
  evalTactic (← `(tactic|
    funext _x;
    apply $h
  ))

elab "funext_cl_" : tactic => do
  evalTactic (← `(tactic|
    apply funext;
    assumption
  ))

elab "_funext_cl_" : tactic => do
  evalTactic (← `(tactic|
    apply funext
  ))


elab "_funext_cl" h:term "," h_new:ident : tactic => do
  evalTactic (← `(tactic|
    have $h_new : _ = _ := funext $h
  ))


def exists_unique {T : Type} (P : T → Prop) : Prop := (∃ (x : T), P x ∧ (∀ y : T, (P y → x = y)))


open Lean TSyntax.Compat in
macro "∃!" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``exists_unique xs b


@[app_unexpander exists_unique] def unexpandexists_unique: Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident ↦ ∃! $xs:binderIdent*, $b) => `(∃! $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident ↦ $b)                      => `(∃! $x:ident, $b)
  | `($(_) fun ($x:ident : $t) ↦ $b)               => `(∃! ($x:ident : $t), $b)
  | _                                               => throw ()



elab "intro_exists_unique" h:term : tactic => do
  evalTactic (← `(tactic|
    intro_exists $h;
    try dsimp (config := { beta := true, zeta := false, iota := false })
  ))


elab "intro_exists_unique" x:term : tactic => do
  evalTactic (← `(tactic|
    intro_exists $x;
    try dsimp (config := { beta := true, zeta := false, iota := false })
  ))


elab "intro_exists_unique_" x:term "," hex:term "," hun:term : tactic => do
  evalTactic (← `(tactic|
    intro_exists $x;
    (try dsimp (config := { beta := true, zeta := false, iota := false }));
    intro_and_ $hex, $hun
  ))




syntax "_intro_exists_unique" term "," term "," term "," ident : tactic
elab_rules : tactic
  | `(tactic| _intro_exists_unique $x, $hex, $hun, $h_new) => do
    let xExpr   ← elabTerm x   none
    let hexExpr ← elabTerm hex none
    let hunExpr ← elabTerm hun none

    let andExpr ← mkAppM ``And.intro #[hexExpr, hunExpr]
    let andType ← inferType andExpr
    let predExpr ← mkLambdaFVars #[xExpr] andType

    let currentExpr ← mkAppOptM ``Exists.intro #[none, some predExpr, some xExpr, some andExpr]
    let type ← inferType currentExpr

    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.assert h_new.getId type currentExpr
      let (_, mvarIdPost) ← mvarIdNew.intro1P
      return [mvarIdPost]

macro "elim_exists_unique" h:term "," a:ident "," hpa:ident "," hfora:ident : tactic =>
  `(tactic|
      (
        let ⟨$a, ⟨$hpa, $hfora⟩⟩ := $h
        try dsimp (config := { beta := true, zeta := false, iota := false }) at $hpa $hfora;
      )
  )

macro "elim_exists_unique" h:term "," a:ident "," hpa:ident "," hfora:ident : tactic =>
  `(tactic|
      (
        let ⟨$a, ⟨$hpa, $hfora⟩⟩ := $h
        try dsimp (config := { beta := true, zeta := false, iota := false }) at $hpa $hfora;
      )
  )


macro "elim_exists_uniquec" h:term "," a:ident "," hpa:ident "," hfora:ident : tactic =>
  `(tactic|
      (
        let ⟨$a, ⟨$hpa, $hfora⟩⟩ := $h
        try dsimp (config := { beta := true, zeta := false, iota := false }) at $hpa $hfora;
        clear $h
      )
  )


elab "elim_exists_unique_" h:term "," hq:term : tactic => do
  evalTactic (← `(tactic|
     let ⟨_a, ⟨_Hpa, _HFra⟩⟩ := $h;
      specialize ($hq _a);
      apply $hq;
      assumption
  ))


elab "_elim_exists_unique" h:term "," Q:term "," newH:ident : tactic => do
  let hExpr ← elabTerm h none
  let hType ← inferType hExpr
  let hType ← whnf hType

  let (fn, args) := hType.getAppFnArgs

  if fn == ``Exists && args.size == 2 then
    let pExpr := args[1]!
    let qExpr ← elabTerm Q none

    let predType ← inferType pExpr
    let xType := predType.bindingDomain!

    let innerForallExpr ← Meta.withLocalDecl `x BinderInfo.default xType fun x => do
      let pApp := mkApp pExpr x
      let pAppRed ← whnf pApp
      let pxOnly := pAppRed.appFn!.appArg!
      let pxQ ← mkArrow pxOnly qExpr
      mkForallFVars #[x] pxQ

    let fullTypeExpr ← mkArrow innerForallExpr qExpr
    let fullTypeExpr ← reduce fullTypeExpr

    let fullTypeSyntax ← delab fullTypeExpr

    evalTactic (← `(tactic|
       (have $newH : $fullTypeSyntax := by
          let ⟨_a, _Hpa, _HFra⟩ := $h
          intro _h_forq
          apply (_h_forq _a)
          exact _Hpa
       );
       try dsimp (config := { beta := true, zeta := false, iota := false }) at $(← `(Lean.Parser.Tactic.locationHyp| $newH:ident))
    ))
  else
    throwError "Hypothesis {h} is not an existential (expected Exists P)."
