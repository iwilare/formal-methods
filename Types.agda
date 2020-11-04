open import Data.Nat     using (ℕ) renaming (_+_ to _+ᵢ_; _≤?_ to _≤?ᵢ_)
open import Agda.Builtin.Float renaming (primFloatPlus to _+ᵣ_; primFloatLess to _≤?ᵣ_)
open import Data.Bool    using (Bool; true; false; not; _∧_)
open import Data.Sum     using (inj₁; inj₂; _⊎_)
open import Data.Product using (_×_; _,_; -,_; _-,-_; ∃; ∃-syntax; proj₂)
open import Data.String  using (String; _≟_)
open import Relation.Nullary           using (¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Negation  using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

vname = String
int = ℕ
real = Float
bool = Bool

data val : Set where
  Iv : int  → val
  Rv : real → val

data aexp : Set where
  Ic   : int   → aexp
  Rc   : real  → aexp
  V    : vname → aexp
  Plus : aexp  → aexp → aexp

data bexp : Set where
  Bc   : Bool → bexp
  Not  : bexp → bexp
  And  : bexp → bexp → bexp
  Less : aexp → aexp → bexp
  
data com : Set where
  SKIP  : com
  _::=_ : String → aexp → com
  _::_  : com → com → com
  IF_THEN_ELSE_ : bexp → com → com → com
  WHILE_DO_     : bexp → com → com

data ty : Set where
  Ity : ty
  Rty : ty

tyenv = vname → ty
state = vname → val

_[_::=_] : state → vname → val → state
(s [ X ::= n ]) Y with Y ≟ X
... | yes _ = n
... | no  _ = s Y

data _⊢ₐ_∷_ : tyenv → aexp → ty → Set where
  taexpI : ∀{Γ i} → Γ ⊢ₐ Ic i ∷ Ity
  taexpR : ∀{Γ r} → Γ ⊢ₐ Rc r ∷ Rty
  taexpV : ∀{Γ x} → Γ ⊢ₐ V x ∷ Γ x
  taexpP : ∀{Γ a₁ a₂ τ}
      → Γ ⊢ₐ a₁ ∷ τ
      → Γ ⊢ₐ a₂ ∷ τ
      → Γ ⊢ₐ Plus a₁ a₂ ∷ τ

data _⊢₆_ : tyenv → bexp → Set where
  tbexpC : ∀{Γ v} → Γ ⊢₆ Bc v
  tbexpN : ∀{Γ b} → Γ ⊢₆ b
                   → Γ ⊢₆ Not b
  tbexpA : ∀{Γ b₁ b₂}
      → Γ ⊢₆ b₁
      → Γ ⊢₆ b₂
      → Γ ⊢₆ And b₁ b₂
  tbexpL : ∀{Γ a₁ a₂ τ}
      → Γ ⊢ₐ a₁ ∷ τ
      → Γ ⊢ₐ a₂ ∷ τ
      → Γ ⊢₆ Less a₁ a₂

data _⊢_ : tyenv → com → Set where
  TSkip : ∀{Γ} → Γ ⊢ SKIP
  TLoc : ∀{Γ a x} → Γ ⊢ₐ a ∷ Γ x
                 → Γ ⊢ (x ::= a)
  TSeq : ∀{Γ c₁ c₂}
       → Γ ⊢ c₁
       → Γ ⊢ c₂
       → Γ ⊢ (c₁ :: c₂)
  TIf : ∀{Γ b c₁ c₂}
      → Γ ⊢₆ b
      → Γ ⊢ c₁
      → Γ ⊢ c₂
      → Γ ⊢ (IF b THEN c₁ ELSE c₂)
  TWhile : ∀{Γ b c}
         → Γ ⊢₆ b
         → Γ ⊢ c
         → Γ ⊢ (WHILE b DO c)


type : val → ty
type (Iv i) = Ity
type (Rv r) = Rty

_⊢ₛ_ : tyenv → state → Set
Γ ⊢ₛ s = ∀ x → type (s x) ≡ Γ x


data taval : aexp → state → val → Set where
  tavalI : ∀{i s}
         → taval (Ic i) s (Iv i)
  tavalR : ∀{r s}
         → taval (Rc r) s (Rv r)
  tavalV : ∀{x s}
         → taval (V x) s (s x)
  tavalSI : ∀{s a₁ a₂ i₁ i₂}
          → taval a₁ s (Iv i₁)
          → taval a₂ s (Iv i₂)
          → taval (Plus a₁ a₂) s (Iv (i₁ +ᵢ i₂))
  tavalSR : ∀{s a₁ a₂ r₁ r₂}
          → taval a₁ s (Rv r₁)
          → taval a₂ s (Rv r₂)
          → taval (Plus a₁ a₂) s (Rv (r₁ +ᵣ r₂))

data tbval : bexp → state → bool → Set where
  tbvalC : ∀{s v}
         → tbval (Bc v) s v
  tbvalN : ∀{s b bv}
         → tbval b s bv
         → tbval (Not b) s (not bv)
  tbvalA : ∀{s b₁ b₂ bv₁ bv₂}
         → tbval b₁ s bv₁
         → tbval b₂ s bv₂
         → tbval (And b₁ b₂) s (bv₁ ∧ bv₂)
  tbvalLI : ∀{s a₁ a₂ i₁ i₂}
         → taval a₁ s (Iv i₁)
         → taval a₂ s (Iv i₂)
         → tbval (Less a₁ a₂) s (⌊ i₁ ≤?ᵢ i₂ ⌋)
  tbvalLR : ∀{s a₁ a₂ r₁ r₂}
         → taval a₁ s (Rv r₁)
         → taval a₂ s (Rv r₂)
         → tbval (Less a₁ a₂) s (r₁ ≤?ᵣ r₂)

data ⦅_,_⦆→⦅_,_⦆ : com → state → com → state → Set where
  Loc : ∀{x a s v}
      → taval a s v
      → ⦅ x ::= a , s ⦆→⦅ SKIP , s [ x ::= v ] ⦆
  Comp₁ : ∀{c s}
        → ⦅ SKIP :: c , s ⦆→⦅ c , s ⦆
  Comp₂ : ∀{c₁ c₁′ c₂ s s′}
        →  ⦅ c₁       , s ⦆→⦅ c₁′       , s′ ⦆
        →  ⦅ c₁ :: c₂ , s ⦆→⦅ c₁′ :: c₂ , s′ ⦆
  IfTrue  : ∀{b s c₁ c₂}
          → tbval b s true
          → ⦅ IF b THEN c₁ ELSE c₂ , s ⦆→⦅ c₁ , s ⦆
  IfFalse : ∀{b s c₁ c₂}
          → tbval b s false
          → ⦅ IF b THEN c₁ ELSE c₂ , s ⦆→⦅ c₂ , s ⦆           
  While : ∀{b s c}
        → ⦅ WHILE b DO c , s ⦆→⦅ IF b THEN (c :: (WHILE b DO c)) ELSE SKIP , s ⦆


data  ⦅_,_⦆→*⦅_,_⦆ : com → state → com → state → Set where
  Ref : ∀{c s} → ⦅ c , s ⦆→*⦅ c , s ⦆
  Step : ∀{c c′ c² s s′ s²}
       → ⦅ c  , s  ⦆→⦅ c′ , s′ ⦆
       → ⦅ c′ , s′ ⦆→*⦅ c² , s² ⦆
       → ⦅ c  , s  ⦆→*⦅ c² , s² ⦆

trans : ∀{c c′ c² s s′ s²}
      → ⦅ c  , s  ⦆→*⦅ c′ , s′ ⦆
      → ⦅ c′ , s′ ⦆→*⦅ c² , s² ⦆
      → ⦅ c  , s  ⦆→*⦅ c² , s² ⦆
trans Ref b = b
trans (Step x a) b = Step x (trans a b)       


preservation-aval : ∀{Γ a s τ v}
  → Γ ⊢ₐ a ∷ τ
  → Γ ⊢ₛ s
  → taval a s v
  → type v ≡ τ
preservation-aval taexpI b tavalI = refl
preservation-aval taexpR b tavalR = refl
preservation-aval taexpV b (tavalV {x}) = b x
preservation-aval (taexpP a a₁) b (tavalSI c c₁) = preservation-aval a₁ b c₁
preservation-aval (taexpP a a₁) b (tavalSR c c₁) = preservation-aval a₁ b c₁

extract-ity : ∀ v
  → type v ≡ Ity
  → ∃[ i ] (v ≡ Iv i)
extract-ity (Iv x) r = x , refl 

extract-rty : ∀ v
  → type v ≡ Rty
  → ∃[ i ] (v ≡ Rv i)
extract-rty (Rv x) r = x , refl

progress-aval : ∀{Γ a s τ}
  → Γ ⊢ₐ a ∷ τ
  → Γ ⊢ₛ s
  → ∃[ v ] (taval a s v)
progress-aval taexpI b = -, tavalI
progress-aval taexpR b = -, tavalR
progress-aval taexpV b = -, tavalV
progress-aval {τ = Ity} (taexpP a₁ a₂) b with progress-aval a₁ b | progress-aval a₂ b
... | rv , r  | mv , m with extract-ity rv (preservation-aval a₁ b r)
                          | extract-ity mv (preservation-aval a₂ b m)
... | v1 , e1 | v2 , e2 rewrite e1 | e2 = -, tavalSI r m
progress-aval {τ = Rty} (taexpP a₁ a₂) b with progress-aval a₁ b | progress-aval a₂ b
... | rv , r  | mv , m with extract-rty rv (preservation-aval a₁ b r)
                          | extract-rty mv (preservation-aval a₂ b m)
... | v1 , e1 | v2 , e2 rewrite e1 | e2 = -, tavalSR r m


progress-bval : ∀{Γ b s}
  → Γ ⊢₆ b
  → Γ ⊢ₛ s
  → ∃[ v ] (tbval b s v)
progress-bval tbexpC x₁ = -, tbvalC
progress-bval (tbexpN x) x₁ = -, tbvalN (proj₂ (progress-bval x x₁))
progress-bval (tbexpA a b) x = -, tbvalA (proj₂ (progress-bval a x))
                                         (proj₂ (progress-bval b x))
progress-bval (tbexpL {τ = Ity} a₁ a₂) b with progress-aval a₁ b | progress-aval a₂ b
... | rv , r  | mv , m with extract-ity rv (preservation-aval a₁ b r)
                          | extract-ity mv (preservation-aval a₂ b m)
... | v1 , e1 | v2 , e2 rewrite e1 | e2 = -, tbvalLI r m
progress-bval (tbexpL {τ = Rty} a₁ a₂) b with progress-aval a₁ b | progress-aval a₂ b
... | rv , r  | mv , m with extract-rty rv (preservation-aval a₁ b r)
                          | extract-rty mv (preservation-aval a₂ b m)
... | v1 , e1 | v2 , e2 rewrite e1 | e2 = -, tbvalLR r m


preservation-com : ∀{Γ c s c′ s′}
  → ⦅ c , s ⦆→⦅ c′ , s′ ⦆
  → Γ ⊢ c
  → Γ ⊢ c′
preservation-com (Loc x₁) (TLoc x₂) = TSkip
preservation-com Comp₁ (TSeq b b₁) = b₁
preservation-com (Comp₂ a) (TSeq b b₁) = TSeq (preservation-com a b) b₁
preservation-com (IfTrue x) (TIf x₁ b b₁) = b
preservation-com (IfFalse x) (TIf x₁ b b₁) = b₁
preservation-com While (TWhile x b) = TIf x (TSeq b (TWhile x b)) TSkip


preservation-state : ∀{Γ c s c′ s′}
  → ⦅ c , s ⦆→⦅ c′ , s′ ⦆
  → Γ ⊢ c
  → Γ ⊢ₛ s
  → Γ ⊢ₛ s′
preservation-state (Loc {x₃} x₁) (TLoc x₂) r x₄ with x₄ ≟ x₃
... | no ¬p = r x₄
... | yes p with preservation-aval x₂ r x₁
... | z rewrite p = z
preservation-state Comp₁ (TSeq c c₁) r = r
preservation-state (Comp₂ d) (TSeq c c₁) r = preservation-state d c r
preservation-state (IfTrue x) (TIf x₁ c c₁) r = r
preservation-state (IfFalse x) (TIf x₁ c c₁) r = r
preservation-state While (TWhile x c) r = r


preservation : ∀{Γ c s c′ s′}
  → Γ ⊢  c
  → Γ ⊢ₛ s
  → ⦅ c , s ⦆→⦅ c′ , s′ ⦆
  → Γ ⊢ c′ × Γ ⊢ₛ s′
preservation a b c = preservation-com c a , preservation-state c a b


either-skip : ∀ c
            → c ≡ SKIP ⊎ ¬ c ≡ SKIP
either-skip SKIP = inj₁ refl
either-skip (x ::= x₁) = inj₂ (λ ())
either-skip (c :: c₁) = inj₂ (λ ())
either-skip (IF x THEN c ELSE c₁) = inj₂ (λ ())
either-skip (WHILE x DO c) = inj₂ (λ ())


progress : ∀{Γ c s}
  → Γ ⊢  c
  → Γ ⊢ₛ s
  → ¬ c ≡ SKIP
  → ∃[ c′ ] (∃[ s′ ] ( ⦅ c , s ⦆→⦅ c′ , s′ ⦆ ))
progress TSkip b c = contradiction refl c
progress {s = s} (TLoc x) b _ = SKIP , -, Loc (proj₂ (progress-aval x b))
progress {s = s} (TSeq {_}{c₁}{c₂} a a₁) b _ with either-skip c₁
... | inj₁  skip rewrite skip = c₂ , s , Comp₁
... | inj₂ ¬skip = let c₁′       , s′ ,       r = progress a b ¬skip
                    in c₁′ :: c₂ , s′ , Comp₂ r
progress (TIf x a a₁) b _ with progress-bval x b
... | false , tb = -, -, IfFalse tb
... | true  , tb = -, -, IfTrue tb
progress (TWhile x a) b _ = -, -, While


type-soundness : ∀{c s c′ s′ Γ}
  → ⦅ c , s ⦆→*⦅ c′ , s′ ⦆
  → Γ ⊢  c
  → Γ ⊢ₛ s
  → ¬ c′ ≡ SKIP
  → ∃[ c″ ] (∃[ s″ ] ( ⦅ c′ , s′ ⦆→⦅ c″ , s″ ⦆ ))
type-soundness Ref c d e =  progress c d e
type-soundness (Step x r) c d e with preservation c d x
... | ct , st = type-soundness r ct st e
