import Props2Theories.TacticNames
open Lean Elab Tactic Meta PrettyPrinter Delaborator SubExpr

axiom Set : Type
axiom belongs : Set → Set → Prop
infix:50 " ∈ " => belongs
notation:50 x " ∉ " s => ¬(belongs x s)

@[delab app.Not]
def delabNotMem : Delab := do
  let e ← getExpr
  if e.isAppOfArity ``Not 1 then
    let arg := e.appArg!
    if arg.isAppOfArity ``belongs 2 then
      let x ← withAppArg do withAppFn do withAppArg delab
      let s ← withAppArg do withAppArg delab
      return ← `($x ∉ $s)
  failure

axiom iota_op {P : Set → Prop} (h : ∃! x, P x) : Set
axiom iota_pr {P : Set → Prop} (h : ∃! x, P x) : P (iota_op h)
axiom iota_e {P : Set → Prop} (h : ∃! x, P x) (a : Set) (g : P a) : a = iota_op h





def forall_in_A (P : Set → Prop) (A : Set) : Prop := ∀ x, x ∈ A → P x
syntax (name := forall_in) (priority := high) "∀ " ident+ " ∈ " term " , " term : term
macro_rules (kind := forall_in)
  | `(∀ $x:ident ∈ $A , $p) => `(forall_in_A (fun $x => $p) $A)
  | `(∀ $x:ident $xs:ident $rest:ident* ∈ $A , $p) => `(forall_in_A (fun $x => ∀ $xs $rest* ∈ $A , $p) $A)

def exists_in_A (P : Set → Prop) (A : Set) : Prop := ∃ x, x ∈ A ∧ P x
syntax (name := exists_in) (priority := high) "∃ " ident+ " ∈ " term " , " term : term
macro_rules (kind := exists_in)
  | `(∃ $x:ident ∈ $A , $p) => `(exists_in_A (fun $x => $p) $A)
  | `(∃ $x:ident $xs:ident $rest:ident* ∈ $A , $p) => `(exists_in_A (fun $x => ∃ $xs $rest* ∈ $A , $p) $A)

def exists_uniq_in_A (P : Set → Prop) (A : Set) : Prop := ∃ w, (w ∈ A ∧ P w) ∧ (∀ y ∈ A , P y → w = y)
syntax (name := exists_uniq_in) (priority := high) "∃! " ident+ " ∈ " term " , " term : term
macro_rules (kind := exists_uniq_in)
  | `(∃! $x:ident ∈ $A , $p) => `(exists_uniq_in_A (fun $x => $p) $A)
  | `(∃! $x:ident $xs:ident $rest:ident* ∈ $A , $p) => `(exists_uniq_in_A (fun $x => ∃! $xs $rest* ∈ $A , $p) $A)

@[app_unexpander forall_in_A]
def unexpandForallInA : Unexpander
  | `($(_) $f $A) =>
    match f with
    | `(fun $x:ident => $p) => `(∀ $x ∈ $A, $p)
    | _ => throw ()
  | _ => throw ()

@[app_unexpander exists_in_A]
def unexpandExistsInA : Unexpander
  | `($(_) $f $A) =>
    match f with
    | `(fun $x:ident => $p) => `(∃ $x ∈ $A, $p)
    | _ => throw ()
  | _ => throw ()

@[app_unexpander exists_uniq_in_A]
def unexpandExistsUniqInA : Unexpander
  | `($(_) $f $A) =>
    match f with
    | `(fun $x:ident => $p) => `(∃! $x ∈ $A, $p)
    | _ => throw ()
  | _ => throw ()




elab "specialize_in" h:ident "," x:term : tactic => do
  evalTactic (← `(tactic|
    specialize $h $x;
    try dsimp (config := { beta := true, zeta := false, iota := false }) at $h:ident
  ))

elab "specialize_in_" h:ident "," x:term "," hx:term : tactic => do
  evalTactic (← `(tactic|
    specialize $h $x $hx;
    try dsimp (config := { beta := true, zeta := false, iota := false }) at $h:ident
  ))

elab "intro_in" x:ident : tactic => do
  evalTactic (← `(tactic|
    intro $x:ident;
    try dsimp (config := { beta := true, zeta := false, iota := false })

  ))

elab "intro_in_" x:ident "," hx:ident : tactic => do
  evalTactic (← `(tactic|
    intro $x:ident $hx:ident;
    try dsimp (config := { beta := true, zeta := false, iota := false })
  ))


syntax "intro_exists_in" term : tactic
elab_rules : tactic
  | `(tactic| intro_exists_in $arg) => do
    evalTactic (← `(tactic|
    intro_exists $arg;
    (try dsimp (config := { beta := true, zeta := false, iota := false }));
    intro_and

    ))

elab "intro_exists_in_" x:term "," hinx:term "," hpx:term  : tactic => do
  evalTactic (← `(tactic|
    intro_exists_in $x;
    exact $hinx;
    exact $hpx

  ))

syntax "_intro_exists_in" term "," term "," term "," ident : tactic

elab_rules : tactic

  | `(tactic| _intro_exists_in $val, $h_mem, $h_prop, $h_new) => do
    let valExpr ← elabTerm val none
    let hMemExpr ← elabTerm h_mem none
    let hPropExpr ← elabTerm h_prop none
    let andProof ← mkAppM ``And.intro #[hMemExpr, hPropExpr]
    let andType ← inferType andProof
    let abstracted ← kabstract andType valExpr
    let motive ← mkLambdaFVars #[valExpr] abstracted
    let existsProof ← mkAppOptM ``Exists.intro #[none, some motive, some valExpr, some andProof]

    let type ← inferType existsProof
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.assert h_new.getId type existsProof
      let (_, mvarIdPost) ← mvarIdNew.intro1P
      return [mvarIdPost]

macro "elim_exists_in" h:term "," a:ident "," hina:ident "," hpa:ident : tactic =>
  `(tactic|
      (
        let ⟨$a, ⟨$hina, $hpa⟩⟩ := $h
        try dsimp (config := { beta := true, zeta := false, iota := false }) at $hina $hpa
      )
  )

macro "elim_exists_inc" h:term "," a:ident "," hina:ident "," hpa:ident : tactic =>
  `(tactic|
      (
        let ⟨$a, ⟨$hina, $hpa⟩⟩ := $h
        try dsimp (config := { beta := true, zeta := false, iota := false }) at $hina $hpa;
        clear $h
      )
  )

elab "elim_exists_in_" h:term "," hq:term : tactic => do
  evalTactic (← `(tactic|
     let ⟨_a, ⟨_Hina, _HPa⟩⟩ := $h;
      specialize ($hq _a _Hina);
      apply $hq;
      assumption
  ))

elab "_elim_exists_in" h:term "," Q:term "," newH:ident : tactic => do
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
        let (fn2, args2) := pAppRed.getAppFnArgs
        if fn2 == ``And && args2.size == 2 then
          let memExpr := args2[0]!
          let pxExpr  := args2[1]!
          let inner ← mkArrow memExpr (← mkArrow pxExpr qExpr)
          mkForallFVars #[x] inner
        else
          throwError "Expected x ∈ A ∧ P x inside, got: {fn2}"

    let fullTypeExpr ← mkArrow innerForallExpr qExpr
    let fullTypeExpr ← reduce fullTypeExpr

    let fullTypeSyntax ← delab fullTypeExpr

    evalTactic (← `(tactic|
       (have $newH : $fullTypeSyntax := by
          let ⟨_a, _Hmem, _Hpa⟩ := $h
          intro _h_forq
          apply (_h_forq _a _Hmem)
          exact _Hpa
       );
       try dsimp (config := { beta := true, zeta := false, iota := false }) at $(← `(Lean.Parser.Tactic.locationHyp| $newH:ident))
    ))
  else
    throwError "Hypothesis {h} is not an existential (expected ∃ x ∈ A, P x)."



elab "intro_exists_unique_in" h:term : tactic => do
  evalTactic (← `(tactic|
    intro_exists_unique $h;
    try dsimp (config := { beta := true, zeta := false, iota := false })
  ))


elab "intro_exists_unique_in_" x:term "," hinx:term "," hpx:term "," hunique:term  : tactic => do
  evalTactic (← `(tactic|
    intro_exists_unique_in $x;
    intro_and;
    exact And.intro $hinx $hpx;
    exact $hunique

  ))


elab "_intro_exists_unique_in" x:term "," hinx:term "," hpx:term "," hunique:term "," h_new:ident : tactic => do
  let xExpr       ← elabTerm x       none
  let hinxExpr    ← elabTerm hinx    none
  let hpxExpr     ← elabTerm hpx     none
  let huniqueExpr ← elabTerm hunique none

  let andMemProp ← mkAppM ``And.intro #[hinxExpr, hpxExpr]
  let andFull    ← mkAppM ``And.intro #[andMemProp, huniqueExpr]

  let andType    ← inferType andFull
  let abstracted ← kabstract andType xExpr
  let motive     ← mkLambdaFVars #[xExpr] abstracted

  let existsProof ← mkAppOptM ``Exists.intro #[none, some motive, some xExpr, some andFull]


  let hinxType ← inferType hinxExpr
  let aExpr := hinxType.appArg!
  let pxType     ← inferType hpxExpr
  let pAbstracted ← kabstract pxType xExpr
  let pMotive    ← mkLambdaFVars #[xExpr] pAbstracted

  let prettyType ← mkAppM ``exists_uniq_in_A #[pMotive, aExpr]

  liftMetaTactic fun mvarId => do
    let mvarIdNew ← mvarId.assert h_new.getId prettyType existsProof
    let (_, mvarIdPost) ← mvarIdNew.intro1P
    return [mvarIdPost]


macro "elim_exists_unique_in" h:term "," a:ident "," hina:ident "," hpa:ident "," hunique:ident : tactic =>
  `(tactic|
      (
        let ⟨$a, ⟨⟨$hina, $hpa⟩, $hunique⟩⟩ := $h
        try dsimp (config := { beta := true, zeta := false, iota := false }) at $hina $hpa $hunique
      )
  )

macro "elim_exists_unique_inc" h:term "," a:ident "," hina:ident "," hpa:ident "," hunique:ident : tactic =>
  `(tactic|
      (
        let ⟨$a, ⟨⟨$hina, $hpa⟩, $hunique⟩⟩ := $h
        try dsimp (config := { beta := true, zeta := false, iota := false }) at $hina $hpa $hunique;
        clear $h
      )
  )

elab "elim_exists_unique_in_" h:term "," hq:term : tactic => do
  evalTactic (← `(tactic|
     let ⟨_a, ⟨⟨_Hina, _HPa⟩, _Hunique⟩⟩ := $h;
      specialize ($hq _a _Hina);
      apply $hq;
      assumption
  ))


elab "_elim_exists_unique_in" h:term "," Q:term "," newH:ident : tactic => do
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
      let (fn2, args2) := pAppRed.getAppFnArgs
      if fn2 == ``And && args2.size == 2 then
        let leftAnd := args2[0]!
        let leftAndRed ← whnf leftAnd
        let (fn3, args3) := leftAndRed.getAppFnArgs
        if fn3 == ``And && args3.size == 2 then
          let memExpr := args3[0]!
          let pxExpr  := args3[1]!
          let inner ← mkArrow memExpr (← mkArrow pxExpr qExpr)
          mkForallFVars #[x] inner
        else
          throwError "Expected x ∈ A ∧ P x on the left, got: {fn3}"
      else
        throwError "Expected (x ∈ A ∧ P x) ∧ ... inside, got: {fn2}"

    let fullTypeExpr ← mkArrow innerForallExpr qExpr
    let fullTypeExpr ← reduce fullTypeExpr

    let fullTypeSyntax ← delab fullTypeExpr

    evalTactic (← `(tactic|
       (have $newH : $fullTypeSyntax := by
          have _hraw : $(← delab (← whnf (← inferType hExpr))) := $h
          let ⟨_a, ⟨⟨_Hmem, _Hpa⟩, _Hunique⟩⟩ := _hraw
          intro _h_forq
          apply (_h_forq _a _Hmem)
          exact _Hpa
       );
       try dsimp (config := { beta := true, zeta := false, iota := false }) at $(← `(Lean.Parser.Tactic.locationHyp| $newH:ident))
    ))
  else
    throwError "Hypothesis {h} is not an existential (expected ∃! x ∈ A, P x)."



-- ZF axioms
axiom regularity_ax : ∀ A, (∃ x, x ∈ A) → ∃ B ∈ A, ∀ x ∈ B, x ∉ A
axiom set_extensionality_ax : ∀ A B, (∀ x, (x ∈ A ↔ x ∈ B)) → (A = B)
axiom emp_st_ax : ∃ A, (∀ x, x ∉ A)
axiom boolean_ax : ∀ A, ∃ B, ∀ x, (x ∈ B ↔ (∀ s ∈ x, s ∈ A))
axiom union_ax : ∀ A, ∃ B, ∀ x, (x ∈ B ↔ (∃ y ∈ A, x ∈ y))
axiom replacement_ax (P : Set → Set → Prop) :
∀ A, (∀ x, ∀ y, ∀ z, P x y → P x z → y = z) -> ∃ B, ∀ y, (y ∈ B ↔ ∃ x ∈ A, P x y)
axiom infinity_ax : ∃ A, (∀ b, (∀ x, x ∉ b) → b ∈ A) ∧
(∀ x ∈ A, ∀ y, (∀ t, (t ∈ y ↔ t ∈ x ∨ t = x)) → y ∈ A)

-- ZFC choice axiom
axiom choice_ax : ∀ A,
  (∀ t ∈ A, ∃ r, r ∈ t) →
  (∀ B, (∀ x, (x ∈ B ↔ ∃ y ∈ A, x ∈ y)) →
    ∃ f,
      (∀ m ∈ f, ∃ x ∈ A, ∃ y ∈ B,
        (∀ n, n ∈ m ↔ (∀ k, k ∈ n ↔ (k = x ∨ k = y)) ∨ (∀ k, k ∈ n ↔ k = x))) ∧
      (∀ x ∈ A, ∃! y ∈ B, ∃ pr ∈ f,
        (∀ m, m ∈ pr ↔ (∀ n, n ∈ m ↔ (n = x ∨ n = y)) ∨ (∀ n, n ∈ m ↔ n = x))) ∧
      (∀ x ∈ A, ∀ y ∈ B, ∀ pr,
        (∀ m, m ∈ pr ↔ (∀ n, n ∈ m ↔ (n = x ∨ n = y)) ∨ (∀ n, n ∈ m ↔ n = x)) →
        pr ∈ f → y ∈ x))

-- TG Tarksi axiom
axiom tarski_ax : ∀ A, ∃ U,
(A ∈ U) ∧
(∀ s ∈ U, ∀ y, (∀ t ∈ y, t ∈ s) → y ∈ U) ∧
(∀ s ∈ U, ∀ P, (∀ t, (t ∈ P) ↔ (∀ k ∈ t, k ∈ s)) → P ∈ U)
∧
(∀ s, (∀ t ∈ s, t ∈ U) → (
  ¬∃ f, (
    (∀ m ∈ f, ∃ x ∈ s, ∃ y ∈ U,
        (∀ n, n ∈ m ↔ (∀ k, k ∈ n ↔ (k = x ∨ k = y)) ∨ (∀ k, k ∈ n ↔ k = x)))
    ∧
    (∀ x ∈ s, ∃ y ∈ U, ∃! pr ∈ f,
        (∀ m, m ∈ pr ↔ (∀ n, n ∈ m ↔ (n = x ∨ n = y)) ∨ (∀ n, n ∈ m ↔ n = x)))
    ∧
    (∀ y ∈ U, ∃ x ∈ s, ∃! pr ∈ f,
        (∀ m, m ∈ pr ↔ (∀ n, n ∈ m ↔ (n = x ∨ n = y)) ∨ (∀ n, n ∈ m ↔ n = x)))
  )
) → s ∈ U)
