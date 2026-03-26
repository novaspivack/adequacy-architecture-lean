/-
  **SPEC_029_FR1 — FE-3:** branch-generic phantom-indexed semantic certificate / forgetful transport.

  **Sorts.** `W` and `B` live in **`Type u`** (use a wrapper when the native outer layer is **`Prop`**).
  Certificates `IC w` and summit payload `R` may be **`Prop`** or **`Type`** — hence **`Sort v` / `Sort r`**.
-/

universe u v r

namespace AdequacyArchitecture.Portability

namespace BranchGenericSemanticTransport

variable {W B : Type u} {R : Sort r} {IC : W → Sort v}

structure IndexedPhantomCertificateOps (W B : Type u) (IC : W → Sort v) (R : Sort r) where
  indexed : ∀ w, B → IC w
  summitReportOf : ∀ w, IC w → R
  agreedSummit : B → R

abbrev ForgetfulIndexedCoherent (ops : IndexedPhantomCertificateOps W B IC R) : Prop :=
  ∀ w b, ops.summitReportOf w (ops.indexed w b) = ops.agreedSummit b

abbrev ForgetfulAgreementInjects (ops : IndexedPhantomCertificateOps W B IC R) : Prop :=
  ∀ w_a w_b b₁ b₂,
    ops.summitReportOf w_a (ops.indexed w_a b₁) = ops.summitReportOf w_b (ops.indexed w_b b₂) →
      ops.agreedSummit b₁ = ops.agreedSummit b₂

structure Core (W B : Type u) (IC : W → Sort v) (R : Sort r) where
  ops : IndexedPhantomCertificateOps W B IC R
  forget_coherent : ForgetfulIndexedCoherent ops
  forget_injects : ForgetfulAgreementInjects ops

/--
  **SPEC_032 Stage C2 — FE-3 functoriality (bundle side):** precompose the **`B`**-argument of **`indexed`** and
  **`agreedSummit`** along **`f : B' → B`**.

  This is the **honest** “pull FE-3 ops back along **`f`**” — it **never** mentions Adequacy compare **`π : γ → α`**.
  Composing with representation pullback needs an **explicit** **`f`** (see **`Instances/RepresentationNemsStageC2`**
  **`NemsFe3SummitBundleCompareSection`**).
-/
def indexedPhantomCertificateOps_pullbackAlongDom {W B B' : Type u} {IC : W → Sort v} {R : Sort r}
    (f : B' → B) (ops : IndexedPhantomCertificateOps W B IC R) :
    IndexedPhantomCertificateOps W B' IC R where
  indexed := fun w b' => ops.indexed w (f b')
  summitReportOf := ops.summitReportOf
  agreedSummit := fun b' => ops.agreedSummit (f b')

theorem forgetfulIndexedCoherent_of_indexedPhantomCertificateOps_pullbackAlongDom
    {W B B' : Type u} {IC : W → Sort v} {R : Sort r}
    (f : B' → B) (ops : IndexedPhantomCertificateOps W B IC R)
    (h : ForgetfulIndexedCoherent ops) :
    ForgetfulIndexedCoherent (indexedPhantomCertificateOps_pullbackAlongDom f ops) := by
  intro w b'
  exact h w (f b')

theorem forgetfulAgreementInjects_of_indexedPhantomCertificateOps_pullbackAlongDom
    {W B B' : Type u} {IC : W → Sort v} {R : Sort r}
    (f : B' → B) (ops : IndexedPhantomCertificateOps W B IC R)
    (h : ForgetfulAgreementInjects ops) :
    ForgetfulAgreementInjects (indexedPhantomCertificateOps_pullbackAlongDom f ops) := by
  intro w_a w_b b₁ b₂ hsr
  exact h w_a w_b (f b₁) (f b₂) hsr

/--
  **SPEC_032 Phase D:** pulling back along the identity map on **`B`** returns **`ops`**.
-/
theorem indexedPhantomCertificateOps_pullbackAlongDom_id
    {W B : Type u} {IC : W → Sort v} {R : Sort r}
    (ops : IndexedPhantomCertificateOps W B IC R) :
    indexedPhantomCertificateOps_pullbackAlongDom (fun b : B => b) ops = ops := by
  rcases ops with ⟨idx, sr, ag⟩
  dsimp only [indexedPhantomCertificateOps_pullbackAlongDom]

/--
  **SPEC_032 Phase D:** pullbacks **compose** — precomposition in the bundle slot is functorial.
-/
theorem indexedPhantomCertificateOps_pullbackAlongDom_comp
    {W B B' B'' : Type u} {IC : W → Sort v} {R : Sort r}
    (ops : IndexedPhantomCertificateOps W B IC R)
    (f : B' → B) (g : B'' → B') :
    indexedPhantomCertificateOps_pullbackAlongDom (f ∘ g) ops =
      indexedPhantomCertificateOps_pullbackAlongDom g (indexedPhantomCertificateOps_pullbackAlongDom f ops) := by
  rcases ops with ⟨idx, sr, ag⟩
  dsimp only [indexedPhantomCertificateOps_pullbackAlongDom, Function.comp_apply]

/--
  **SPEC_032 — π / bridge hygiene:** pointwise-equal **`B' → B`** maps yield **definitionally equal** pulled-back ops
  (used to relate **`effectiveProj`** to **`j ∘ π`** once a **semantic triangle** is declared).
-/
theorem indexedPhantomCertificateOps_pullbackAlongDom_congr_dom
    {W B B' : Type u} {IC : W → Sort v} {R : Sort r}
    {f g : B' → B} (ops : IndexedPhantomCertificateOps W B IC R) (h : ∀ x, f x = g x) :
    indexedPhantomCertificateOps_pullbackAlongDom f ops =
      indexedPhantomCertificateOps_pullbackAlongDom g ops := by
  rw [show f = g from funext h]

/--
  **SPEC_032 Phase D:** if **`ops'`** is a **bundle-side pullback** of **`ops`**, then **`summitReportOf`** is unchanged — the
  phantom certificate family **`IC w`** is not reindexed by **`f`** in the **`def`** of **`indexedPhantomCertificateOps_pullbackAlongDom`**.
-/
theorem summitReportOf_eq_of_exists_indexedPhantomCertificateOps_pullbackAlongDom
    {W B B' : Type u} {IC : W → Sort v} {R : Sort r}
    (ops : IndexedPhantomCertificateOps W B IC R)
    (ops' : IndexedPhantomCertificateOps W B' IC R)
    (h : ∃ f : B' → B, ops' = indexedPhantomCertificateOps_pullbackAlongDom f ops) :
    ops'.summitReportOf = ops.summitReportOf := by
  obtain ⟨f, hf⟩ := h
  rw [hf]
  rfl

/--
  **SPEC_032 Phase D — necessity / minimality (bundle-side):** `ops'` equals **`indexedPhantomCertificateOps_pullbackAlongDom f ops`**
  for **some** `f` **iff** `summitReportOf` **agrees** with `ops` **and** **some** `f` **precomposes** `indexed` and **`agreedSummit`**.

  So, once a **fixed** halting-style `ops` is the **host** FE-3 witness, **Law X**-style data is **exactly** a map **`f`**
  satisfying those two **pointwise** families — **`repr` plays no role** (see **`NemsFe3SummitBundleCompareSection`**).
  When **`ops.agreedSummit`** is **injective**, **`f`** is **unique** (**`indexedPhantomCertificateOps_pullbackAlongDom_f_unique_of_eq_pullbacks`**).
-/
theorem exists_indexedPhantomCertificateOps_pullbackAlongDom_iff
    {W B B' : Type u} {IC : W → Sort v} {R : Sort r}
    (ops : IndexedPhantomCertificateOps W B IC R)
    (ops' : IndexedPhantomCertificateOps W B' IC R) :
    (∃ f : B' → B, ops' = indexedPhantomCertificateOps_pullbackAlongDom f ops) ↔
      (ops'.summitReportOf = ops.summitReportOf ∧
        ∃ f : B' → B,
          (∀ (w : W) (b' : B'), ops'.indexed w b' = ops.indexed w (f b')) ∧
            (∀ (b' : B'), ops'.agreedSummit b' = ops.agreedSummit (f b'))) := by
  constructor
  · intro ⟨f, hf⟩
    refine And.intro ?_ ⟨f, ?_, ?_⟩
    · rw [hf]; rfl
    · intro w b'; rw [hf]; rfl
    · intro b'; rw [hf]; rfl
  · rintro ⟨hsr, f, hidx, hag⟩
    refine ⟨f, ?_⟩
    rcases ops with ⟨idx, sr, ag⟩
    rcases ops' with ⟨idx', sr', ag'⟩
    dsimp only [indexedPhantomCertificateOps_pullbackAlongDom]
    have hi : idx' = fun w b' => idx w (f b') := by
      funext w b'
      exact hidx w b'
    have ha : ag' = fun b' => ag (f b') := by
      funext b'
      exact hag b'
    have hsreq : sr' = sr := hsr
    rw [hi, ha, hsreq]

/--
  **SPEC_032 Phase D v3:** if **`ops.agreedSummit`** is **injective** on **`B`**, then two **bundle-side** pullbacks of **`ops`**
  that are **equal as `IndexedPhantomCertificateOps`** come from **equal** maps **`B' → B`**.

  **NEMS note:** **`agreed_summit`** on **`HaltingAnchoredFaithfulSummitMasterBundle`** is **not** injective in general
  (equal **summit report** need not determine the full **bundle**). This lemma is **conditional** — use when a host /
  model **does** satisfy injectivity (e.g. stripped carriers, toy staging).
-/
theorem indexedPhantomCertificateOps_pullbackAlongDom_f_eq_of_agreedSummit_injective
    {W B B' : Type u} {IC : W → Sort v} {R : Sort r}
    (ops : IndexedPhantomCertificateOps W B IC R)
    (h_inj : ∀ b₁ b₂ : B, ops.agreedSummit b₁ = ops.agreedSummit b₂ → b₁ = b₂)
    (f f' : B' → B)
    (h_eq :
      indexedPhantomCertificateOps_pullbackAlongDom f ops =
        indexedPhantomCertificateOps_pullbackAlongDom f' ops) :
    f = f' := by
  refine funext fun b' => h_inj (f b') (f' b') ?_
  simpa [indexedPhantomCertificateOps_pullbackAlongDom] using
    congrArg (fun op : IndexedPhantomCertificateOps W B' IC R => op.agreedSummit b') h_eq

/--
  **SPEC_032 Phase D v3:** same map **`f`** if the **pulled-back** ops are **definitionally** the same witness.
-/
theorem indexedPhantomCertificateOps_pullbackAlongDom_f_unique_of_eq_pullbacks
    {W B B' : Type u} {IC : W → Sort v} {R : Sort r}
    (ops : IndexedPhantomCertificateOps W B IC R)
    (h_inj : ∀ b₁ b₂ : B, ops.agreedSummit b₁ = ops.agreedSummit b₂ → b₁ = b₂)
    (ops' : IndexedPhantomCertificateOps W B' IC R)
    (f f' : B' → B)
    (hf : ops' = indexedPhantomCertificateOps_pullbackAlongDom f ops)
    (hf' : ops' = indexedPhantomCertificateOps_pullbackAlongDom f' ops) :
    f = f' := by
  refine indexedPhantomCertificateOps_pullbackAlongDom_f_eq_of_agreedSummit_injective ops h_inj f f' ?_
  exact hf.symm.trans hf'

/--
  **SPEC_032 Stage C2:** pullback of a full **`Core`** along **`f : B' → B`** (same **`IC`**, **`R`**, **`W`**).
-/
def core_pullbackAlongDom {W B B' : Type u} {IC : W → Sort v} {R : Sort r}
    (f : B' → B) (c : Core W B IC R) : Core W B' IC R where
  ops := indexedPhantomCertificateOps_pullbackAlongDom f c.ops
  forget_coherent :=
    forgetfulIndexedCoherent_of_indexedPhantomCertificateOps_pullbackAlongDom f c.ops c.forget_coherent
  forget_injects :=
    forgetfulAgreementInjects_of_indexedPhantomCertificateOps_pullbackAlongDom f c.ops c.forget_injects

structure PhantomReindexLayer (W B : Type u) (IC : W → Sort v) (R : Sort r)
    (ops : IndexedPhantomCertificateOps W B IC R) where
  reindex : ∀ {w w' : W}, w = w' → IC w → IC w'
  forget_reindex :
    ∀ {w w' : W} (e : w = w') (c : IC w),
      ops.summitReportOf w' (reindex e c) = ops.summitReportOf w c

/--
  Transport a **`PhantomReindexLayer`** back along **`f : B' → B`** — **`reindex`** and **`forget_reindex`** carry
  through because **`summitReportOf`** is unchanged on **`IC w`**.
-/
def phantomReindexLayer_pullbackAlongDom {W B B' : Type u} {IC : W → Sort v} {R : Sort r}
    {ops : IndexedPhantomCertificateOps W B IC R}
    (f : B' → B) (L : PhantomReindexLayer W B IC R ops) :
    PhantomReindexLayer W B' IC R (indexedPhantomCertificateOps_pullbackAlongDom f ops) where
  reindex := L.reindex
  forget_reindex := fun {_ _} e c => L.forget_reindex e c

/-- **SPEC_029 / SPEC_030:** canonical **trivial** `Unit` phantom **`Core`** (shared FE-3 witness for packaging). -/
def fe3TrivialUnitCore : Core Unit Unit (fun _ : Unit => True) True :=
  Core.mk
    ⟨fun _ _ => trivial, fun _ _ => trivial, fun _ => trivial⟩
    (fun _ _ => rfl)
    (fun _ _ _ _ _ => rfl)

end BranchGenericSemanticTransport

end AdequacyArchitecture.Portability
