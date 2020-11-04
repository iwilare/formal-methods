open import Data.Nat    using (ℕ; _+_) renaming (_≤?_ to _≤?ₙ_)
open import Data.Bool   using (Bool; true; false; not; _∧_)
open import Data.String using (String; _≟_)
open import Data.Sum    using (_⊎_; [_,_]′; inj₁; inj₂)
open import Data.Product               using (_×_; _,_)
open import Relation.Nullary           using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Product using (_×_; _,_; -,_; _-,-_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Level using (Level; suc; _⊔_)

open import IMP
open import Hoare

data True {l} : Set l where
  ⊤ : True

data acom {l} : Set (suc l) where
  SKIP  : acom
  _::=_ : String → aexp → acom
  _::_  : acom {l} → acom {l} → acom 
  IF_THEN_ELSE_ : bexp → acom {l} → acom {l} → acom
  WHILE[_]_DO_ : assn {l} → bexp → acom {l} → acom

strip : ∀{l} → acom {l} → com
strip SKIP = SKIP
strip (x ::= a) = x ::= a
strip (c₁ :: c₂) = strip c₁ :: strip c₂
strip (IF b THEN c₁ ELSE c₂) = IF b THEN strip c₁ ELSE strip c₂
strip (WHILE[ I ] b DO c) = WHILE b DO strip c

pre : ∀{l} → acom {l} → assn → assn
pre SKIP Q = Q
pre (x ::= a) Q s = Q (s [ x ::= aval a s ])
pre (c₁ :: c₂) Q = pre c₁ (pre c₂ Q)
pre (IF b THEN c₁ ELSE c₂) Q s with bval b s
... | true = pre c₁ Q s
... | false = pre c₂ Q s
pre (WHILE[ I ] b DO c) Q = I

vc : ∀{l} → acom {l} → assn → Set l
vc SKIP Q = True
vc (x ::= x₁) Q = True
vc (c₁ :: c₂) Q = vc c₁ (pre c₂ Q) × vc c₂ Q
vc (IF b THEN c₁ ELSE c₂) Q = vc c₁ Q × vc c₂ Q
vc (WHILE[ I ] b DO c) Q =
     (∀ s → I s × bval b s ≡ true  → pre c I s)
   × (∀ s → I s × bval b s ≡ false → Q s)
   × vc c I

extract-if-pre₁ : ∀{l} {Q : assn {l}} {c₁ c₂ s} b
  → pre (IF b THEN c₁ ELSE c₂) Q s
  × bval b s ≡ true
  → pre c₁ Q s
extract-if-pre₁ b (x , y) rewrite y = x

extract-if-pre₂ : ∀{l} {Q : assn {l}} {c₁ c₂ s} b
  → pre (IF b THEN c₁ ELSE c₂) Q s
  × bval b s ≡ false
  → pre c₂ Q s
extract-if-pre₂ b (x , y) rewrite y = x

vc-correctness : ∀{l} {P Q : assn} c
  → vc {l} c Q
  → (∀ s → P s → pre c Q s)
  → ⊢[ P ] strip c [ Q ]
vc-correctness SKIP v i = Conseq i Skip (λ s z → z)
vc-correctness (x ::= a) v i = Conseq i Loc (λ r k → k)
vc-correctness (c₁ :: c₂) v i = Comp (vc-correctness c₁ (Data.Product.proj₁ v) i)
                                     (vc-correctness c₂ (Data.Product.proj₂ v) (λ s z → z))
vc-correctness {l}{P}{Q} (IF b THEN c₁ ELSE c₂) (fst , snd) i = 
     Conseq i (If (vc-correctness c₁ fst (λ s p → extract-if-pre₁ b p))
                  (vc-correctness c₂ snd (λ s p → extract-if-pre₂ b p)))
              (λ s z → z)
vc-correctness (WHILE[ I ] b DO c) (fst , fst₁ , snd) i =
    Conseq i (While (vc-correctness c snd fst)) fst₁
   
pre-mono : ∀{l} {P P′ : assn {l}} {s′} c
  → (∀ s → P s → P′ s)
  → pre c P s′ → pre c P′ s′
pre-mono {s′ = s′} SKIP x x₁ = x s′ x₁
pre-mono (x₂ ::= x₃) x x₁ = x _ x₁
pre-mono (c :: c₁) x x₁ = pre-mono c (λ s → pre-mono c₁ x) x₁
pre-mono {s′ = s′} (IF x₂ THEN c₁ ELSE c₂) x x₁ with bval x₂ s′
... | true  = pre-mono c₁ x x₁ 
... | false = pre-mono c₂ x x₁ 
pre-mono (WHILE[ x₂ ] x₃ DO c) x x₁ = x₁

vc-mono : ∀{l} {P P′ : assn {l}} c
  → (∀ s → P s → P′ s)
  → vc c P → vc c P′
vc-mono SKIP _ _ = ⊤
vc-mono (x ::= a) _ _ = ⊤
vc-mono (c₁ :: c₂) pp′ (vcpre , vc2) = vc-mono c₁ (λ _ → pre-mono c₂ pp′) vcpre , vc-mono c₂ pp′ vc2
vc-mono (IF b THEN c₁ ELSE c₂) pp′ (vc₁ , vc₂) = vc-mono c₁ pp′ vc₁ , vc-mono c₂ pp′ vc₂
vc-mono (WHILE[ I ] b DO c) pp′ (I₁ , I₂ , vcc) = I₁ , (λ s z → pp′ s (I₂ s z)) , vcc

either : ∀ c → c ≡ true ⊎ c ≡ false
either true  = inj₁ refl
either false = inj₂ refl

construct-if-pre : ∀{l} {P Q : assn {l}} {ac₁ ac₂} b s
   → (bval b s ≡ true  → pre ac₁ Q s)
   → (bval b s ≡ false → pre ac₂ Q s)
   → pre (IF b THEN ac₁ ELSE ac₂) Q s
construct-if-pre b s f g with bval b s
... | true = f refl
... | false = g refl

vc-completeness : ∀{l} {P Q : assn {l}} c
  → ⊢[ P ] c [ Q ]
  → ∃[ c̃ ] ( c ≡ strip c̃
           × vc c̃ Q
           × (∀ s → P s → pre c̃ Q s))
vc-completeness c Skip = SKIP , refl , ⊤ , (λ x c → c)
vc-completeness c Loc = _ , refl , ⊤ ,  (λ x c → c)
vc-completeness (c₁ :: c₂) (Comp x y) with vc-completeness c₁ x
... | ac₁ , b , c , d                 with vc-completeness c₂ y
... | ac₂ , f , g , h rewrite b | f
                      = (ac₁ :: ac₂) , refl
                      , (vc-mono ac₁ h c , g)
                      , (λ s ps → pre-mono ac₁ h (d s ps))
vc-completeness {P = P} (IF b THEN c₁ ELSE c₂) (If d₁ d₂) with vc-completeness c₁ d₁
... | ac₁ , f , g , h                                     with vc-completeness c₂ d₂
... | ac₂ , j , k , m rewrite f | j
                      = (IF b THEN ac₁ ELSE ac₂) , refl
                      , (g , k)
                      , (λ s ps → construct-if-pre {P = P} b s (λ t → h s (ps , t)) (λ f → m s (ps , f)))
vc-completeness (WHILE b DO c) (While r) with vc-completeness c r
... | ac , f , g , h rewrite f = (WHILE[ _ ] b DO ac) , refl
                               , (h , (λ s z → z) , g)
                               , λ s z → z
vc-completeness c (Conseq x₁ r x₂) with vc-completeness c r
... | ac , f , g , h rewrite f
                     = ac , refl
                     , vc-mono ac x₂ g
                     , (λ s ps → pre-mono ac x₂ (h s (x₁ s ps)))
