open import Prelude.Init; open SetAsType
open import Prelude.General using (true⇒T)
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Membership
open import Prelude.Allable
open import Prelude.InferenceRules

open import EUTxOErr
  hiding (s)
  renaming (S to UTxOSet)
  renaming (_‼_ to _‼ᵐ_)
open import Prelude.Lists.Indexed using (_‼_)

data S : Type where
  ◇ ◆ : S

toggleS : S → S
toggleS = λ where
  ◇ → ◆
  ◆ → ◇

instance
  _ : ToData S
  _ = record {serialise = ser; serialise-inj = serInj; deserialise = deser}
    where
    ser = λ where
      ◇ → "◇"
      ◆ → "◆"

    deser : _
    deser d =
      Nullary.map′
        Sum.[ ◇ ,_ , ◆ ,_ ]
        (λ where (◇ , d≡) → inj₁ d≡; (◆ , d≡) → inj₂ d≡)
        ¿ (d ≡ "◇") ⊎ (d ≡ "◆") ¿

    serInj : Injective≡ ser
    serInj {◇}{◇} refl = refl
    serInj {◆}{◆} refl = refl
    serInj {◇}{◆} ()
    serInj {◆}{◇} ()

-- ** Validator
toggle : Validator
toggle toggle♯ record {inputs = is; outputs = os} _ d
  with deserialise {A = S} d
... | no _ = false
... | yes (s , _) = ⌊ consume◇ ∈? is ⌋ ∧ ⌊ produce◆ ∈? os ⌋
  where
    consume◇ = record
      { outputRef = ⦉ serialise s ♯ ⦊ 1 € at toggle♯
      ; validatorHash = toggle♯
      ; redeemerHash = "" ♯ }
    produce◆ = ⦉ serialise (toggleS s) ♯ ⦊ 1 € at toggle♯
toggle♯ = toggle ♯

-- Fix one direction for now: ◇ ↝ ◆
consume◇ = InputInfo ∋ record
  { outputRef     = ⦉ serialise ◇ ♯ ⦊ 1 € at toggle♯
  ; validatorHash = toggle♯
  ; redeemerHash  = "" ♯ }
produce◆ = OutputInfo ∋
  ⦉ serialise ◆ ♯ ⦊ 1 € at toggle♯

module _
  {r : DATA} {txi : TxInfo}
  (let d = serialise ◇
       record {inputs = is; outputs = os} = txi)
  where

  toggle≡ :
    ∙ consume◇ ∈ is
    ∙ produce◆ ∈ os
      ──────────────────────────
      call toggle txi r d ≡ true
  toggle≡ ◇∈is ◆∈os
    rewrite deserialise∘serialise ◇
          | dec-yes (consume◇ ∈? is) ◇∈is .proj₂
          | dec-yes (produce◆ ∈? os) ◆∈os .proj₂
          = refl
--

t₀ = Tx ∋ record
  { inputs = []
  ; outputs = [ ⦉ serialise ◇ ⦊ 1 € at toggle♯ ]
  ; forge = 1 € }
t₀₀ = (t₀ ♯) indexed-at 0

o  = TxOutput      ∋ ⦉ serialise ◇ ⦊ 1 € at toggle♯
i  = TxInput       ∋ record { outputRef = t₀₀ ; validator = toggle ; redeemer = "" }
ri = ResolvedInput ∋ i , o

t₁ = Tx ∋ record
  { inputs  = [ i ]
  ; outputs = [ ⦉ serialise ◆ ⦊ 1 € at toggle♯ ]
  ; forge   = 0 € }
t₁₀ = (t₁ ♯) indexed-at 0

t₁′ = Tx ∋ record
  { inputs  = [ i ]
  ; outputs = ⦉ serialise ◆ ⦊ 1 € at toggle♯
            ∷ ⦉ serialise ◆ ⦊ 1 € at toggle♯
            ∷ []
  ; forge   = 1 € }
t₁′₀ = (t₁′ ♯) indexed-at 0
t₁′₁ = (t₁′ ♯) indexed-at 1

singleSat doubleSat : L
singleSat = t₀ ∷ t₁  ∷ []
doubleSat = t₀ ∷ t₁′ ∷ []

v₀ : VL ∅ [ t₀ ]
v₀ = t₀
  ⊣ record { noDoubleSpending    = []
           ; validOutputRefs     = []
           ; preservesValues     = refl
           ; allInputsValidate   = []
           ; validateValidHashes = [] }
  ∷ []

s₀ = ⟦ t₀ ⟧₀ ∅

_ = s₀ ≡ singleton (t₀₀ , o)
  ∋ refl

module ⦅1⦆ where
  vor : ∀[ ref ∈ outputRefs t₁ ] (ref ∈ᵈ s₀)
  vor = here refl ∷ []

  rt₁ = Resolved t₁
      ∋ L.All.map (s₀ ‼ᵐ_) vor

  _ = mkUtxo t₀ (here refl) ≡ (t₀₀ , o)
    ∋ refl

  rt≡ : rt₁ ≡ [ o ]
  rt≡ = cong (_∷ []) $ ‼-singleton {k = t₀₀}{o}

  txi  = mkTxInfo t₁ rt₁
  is = txi .TxInfo.inputs
  os = txi .TxInfo.outputs

  ris = ResolvedInputs
      ∋ resolveInputs t₁ rt₁

  postulate ris≡ : ris ≡ [ ri ]
  -- ris≡ rewrite ≟-refl 0 | ≟-refl "" | ≟-refl '◇' = cong [_] (cong (i ,_) refl)

  val≡ : T (call (i .validator) txi (i .redeemer) (o .datum))
  val≡ = true⇒T $
    begin
      call (i .validator) txi (i .redeemer) (o .datum)
    ≡⟨⟩
      toggle toggle♯ txi "" (serialise ◇)
    ≡⟨ toggle≡ {""}{txi}
        ( subst (Any (consume◇ ≡_) ∘ map mkInputInfo) (sym ris≡)
        $ here refl
        )
        (here refl) ⟩
      true
    ∎ where open ≡-Reasoning

  _ : VL ∅ singleSat
  _ = t₀
    ⊣ record
      { noDoubleSpending    = []
      ; validOutputRefs     = []
      ; preservesValues     = refl
      ; allInputsValidate   = []
      ; validateValidHashes = []
      }
    ∷ t₁
    ⊣ record
      { noDoubleSpending    = [] ∷ []
      ; validOutputRefs     = vor
      ; preservesValues     = pv
      ; allInputsValidate   = aiv
      ; validateValidHashes = vvh
      }
    ∷ []
    where
    pv : t₁ .forge + ∑ ris (value ∘ proj₂) ≡ ∑ (t₁ .outputs) value
    pv = cong (λ ⋆ → t₁ .forge + ∑ ⋆ (value ∘ proj₂)) ris≡

    aiv : ∀[ (i , o) ∈ ris ]
      T (call (i .validator) txi (i .redeemer) (o .datum))
    aiv = subst (L.All.All _) (sym ris≡)
        $ val≡ ∷ []

    vvh : ∀[ (i , o) ∈ ris ]
      (o .address ≡ i .validator ♯)
    vvh = subst (L.All.All _) (sym ris≡)
        $ refl ∷ []

  open HoareReasoning -- unsolved metas if inlined in `where` clause :(
  _ =
    begin
      emp
    ~⟨ t₀ ∶- 𝟘⇒𝟙 refl ⟩
      t₀₀ ↦ ⦉ serialise ◇ ⦊ 1 € at toggle♯
    ~⟨ t₁ ∶- 𝟙⇒𝟙 rt₁ val≡ refl ⟩
      t₁₀ ↦ ⦉ serialise ◆ ⦊ 1 € at toggle♯
    ∎

module ⦅12⦆ where
  vor : ∀[ ref ∈ outputRefs t₁′ ] (ref ∈ᵈ s₀)
  vor = here refl ∷ []

  rt₁′ = Resolved t₁′
       ∋ L.All.map (s₀ ‼ᵐ_) vor

  _ = mkUtxo t₀ (here refl) ≡ (t₀₀ , o)
    ∋ refl

  rt≡ : rt₁′ ≡ [ o ]
  rt≡ = cong (_∷ []) $ ‼-singleton {k = t₀₀}{o}

  txi  = mkTxInfo t₁′ rt₁′
  is = txi .TxInfo.inputs
  os = txi .TxInfo.outputs

  ris = ResolvedInputs
      ∋ resolveInputs t₁′ rt₁′

  postulate ris≡ : ris ≡ [ i , o ]
  -- ris≡ rewrite ≟-refl 0 | ≟-refl "" | ≟-refl '◇' = cong [_] (cong (i ,_) refl)

  val≡ : T (call (i .validator) txi (i .redeemer) (o .datum))
  val≡ = true⇒T $
    begin
      call (i .validator) txi (i .redeemer) (o .datum)
    ≡⟨⟩
      toggle toggle♯ txi "" (serialise ◇)
    ≡⟨ toggle≡ {""}{txi}
        ( subst (Any (consume◇ ≡_) ∘ map mkInputInfo) (sym ris≡)
        $ here refl
        )
        (here refl) ⟩
      true
    ∎ where open ≡-Reasoning

  _ : VL ∅ doubleSat
  _ = t₀
    ⊣ record
      { noDoubleSpending    = []
      ; validOutputRefs     = []
      ; preservesValues     = refl
      ; allInputsValidate   = []
      ; validateValidHashes = []
      }
    ∷ t₁′
    ⊣ record
      { noDoubleSpending    = [] ∷ []
      ; validOutputRefs     = vor
      ; preservesValues     = pv
      ; allInputsValidate   = aiv
      ; validateValidHashes = vvh
      }
    ∷ []
    where
    pv : t₁′ .forge + ∑ ris (value ∘ proj₂) ≡ ∑ (t₁′ .outputs) value
    pv = cong (λ ⋆ → t₁′ .forge + ∑ ⋆ (value ∘ proj₂)) ris≡

    aiv : ∀[ (i , o) ∈ ris ]
      T (call (i .validator) txi (i .redeemer) (o .datum))
    aiv = subst (L.All.All _) (sym ris≡)
        $ val≡ ∷ []

    vvh : ∀[ (i , o) ∈ ris ]
      (o .address ≡ i .validator ♯)
    vvh = subst (L.All.All _) (sym ris≡)
        $ refl ∷ []

  open HoareReasoning
  _ =
    begin
      emp
    ~⟨ t₀ ∶- 𝟘⇒𝟙 refl ⟩
      t₀₀ ↦ ⦉ serialise ◇ ⦊ 1 € at toggle♯
    ~⟨ t₁′ ∶- 𝟙⇒𝟚 rt₁′ val≡ refl ⟩
      t₁′₀ ↦ ⦉ serialise ◆ ⦊ 1 € at toggle♯
      ∗
      t₁′₁ ↦ ⦉ serialise ◆ ⦊ 1 € at toggle♯
    ∎

-- ** Rule out double satisfaction

data YesDP (s₀ : UTxOSet) : Type₁ where
  yesDP : ∀ {t txi txi′ txi″ v v′ v″} →
    ⟨ txi  ↦ ⦉ serialise ◇ ⦊ v  € at toggle♯ ⟩ -- ∗ R ⟩
    [ t ]
    ⟨ txi′ ↦ ⦉ serialise ◆ ⦊ v′ € at toggle♯
    ∗ txi″ ↦ ⦉ serialise ◆ ⦊ v″ € at toggle♯ -- ∗ R
    ⟩＠ s₀
    ──────────────────────────────────────────────
    YesDP s₀

yesDP-toggle : ∀ s₀ → YesDP s₀
yesDP-toggle s₀ = yesDP {t = $t} λ Ps₀ →
  let open 𝕄 Ps₀
  in 1⇒2 rt val≡ refl Ps₀
  where
    txi₀ = TxOutputRef ∋ t₀₀

    $o  = TxOutput ∋ ⦉ serialise ◇ ⦊ 1 € at toggle♯
    $i  = TxInput  ∋ record
      { outputRef = txi₀ ; validator = toggle ; redeemer = "" }
    $ri = ResolvedInput ∋ $i , $o

    $t = Tx ∋ record
      { inputs  = [ $i ]
      ; outputs = ⦉ serialise ◆ ⦊ 1 € at toggle♯
                ∷ ⦉ serialise ◆ ⦊ 1 € at toggle♯
                ∷ []
      ; forge   = 1 € }

    module 𝕄 (Ps₀ : (t₀₀ ↦ ⦉ serialise ◇ ⦊ 1 € at toggle♯) s₀) where
      postulate vor : ∀[ ref ∈ outputRefs $t ] (ref ∈ᵈ s₀)
      -- vor = here refl ∷ []

      rt  = Resolved $t
          ∋ L.All.map (s₀ ‼ᵐ_) vor
      txi = mkTxInfo $t rt
      is  = txi .TxInfo.inputs
      os  = txi .TxInfo.outputs
      ris = resolveInputs $t rt

      postulate rt≡ : rt ≡ [ $o ]
      -- rt≡ = cong (_∷ []) $ ‼-singleton {k = txi₀}{o}

      postulate ris≡ : ris ≡ [ ri ]

      val≡ : T $ call toggle txi "" (serialise ◇)
      val≡ = true⇒T $
        begin
          call toggle txi "" (serialise ◇)
        ≡⟨ toggle≡ {""}{txi}
            ( subst (Any (consume◇ ≡_) ∘ map mkInputInfo) (sym ris≡)
            $ here refl
            )
            (here refl) ⟩
          true
        ∎ where open ≡-Reasoning

-- ** Fixed validator
toggle′ : Validator
toggle′ toggle♯ record {inputs = is; outputs = os} _ d
  with deserialise {A = S} d
... | no _ = false
... | yes (s , _) = ⌊ ¿ (is ≡ [ consume◇′ ]) × (os ≡ [ produce◆′ ]) ¿ ⌋
  where
    consume◇′ = record
      { outputRef = ⦉ serialise ◇ ♯ ⦊ 1 € at toggle♯
      ; validatorHash = toggle♯
      ; redeemerHash = "" ♯ }
    produce◆′ = ⦉ serialise ◆ ♯ ⦊ 1 € at toggle♯
toggle′♯ = toggle′ ♯

consume◇′ = InputInfo ∋ record
  { outputRef     = ⦉ serialise ◇ ♯ ⦊ 1 € at toggle′♯
  ; validatorHash = toggle′♯
  ; redeemerHash  = "" ♯ }
produce◆′ = OutputInfo ∋
  ⦉ serialise ◆ ♯ ⦊ 1 € at toggle′♯

module _
  {s : S} {r : DATA} {txi : TxInfo}
  (let d = serialise s
       record {inputs = is; outputs = os} = txi)
  where

  toggle′≡ :
    ∙ is ≡ [ consume◇′ ]
    ∙ os ≡ [ produce◆′ ]
      ───────────────────────────
      call toggle′ txi r d ≡ true
  toggle′≡ refl refl
    rewrite deserialise∘serialise s
          | ≟-refl consume◇′
          | ≟-refl produce◆′
          = refl
--

data NoDP : Type₁ where
  noDP :
    (¬ -- ∃ λ R →
       ∃ λ t →
       ∃ λ txi → ∃ λ txi′ → ∃ λ txi″ →
       ∃ λ v → ∃ λ v′ → ∃ λ v″ →
      ⟨ txi  ↦ ⦉ serialise ◇ ⦊ v  € at toggle′♯ ⟩ -- ∗ R ⟩
      [ t ]
      ⟨ txi′ ↦ ⦉ serialise ◆ ⦊ v′ € at toggle′♯
      ∗ txi″ ↦ ⦉ serialise ◆ ⦊ v″ € at toggle′♯ -- ∗ R
      ⟩)
    ───────────────────────────────────────────────
    NoDP

postulate noDP-toggle′ : NoDP
-- noDP-toggle′ = noDP λ (t , txi , txi′ , txi″ , v , v′ , v″ , p) →
--   let Ps₀ = p {s₀} ({!!} , {!!})
--    in {!!}
