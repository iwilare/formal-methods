open import Data.Nat      using (ℕ; suc; zero; _<_; _≤_; z≤n; s≤s; _+_; _⊔_)
open import Data.Bool     using (Bool; true; false; not; _∧_)
open import Data.Sum      using (inj₁; inj₂; _⊎_; [_,_])
open import Data.Product  using (_×_; _,_; -,_; _-,-_; ∃; ∃-syntax; proj₂)
open import Data.String   using (String; _≟_; length)
open import Relation.Nullary           using (¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans; cong₂)
open import Data.Nat.Properties hiding (_≤?_; _≟_)

open import IMP

level = ℕ

sec : vname → level
-- We can also temporarily use "sec x" to avoid the
-- automatic expansion of the definition in error messages
sec x = length x

secₐ : aexp → level
secₐ (N n) = 0
secₐ (V x) = sec x
secₐ (Plus a b) = secₐ a ⊔ secₐ b

sec₆ : bexp → level
sec₆ (Bc x) = 0
sec₆ (Not b) = sec₆ b
sec₆ (And b₁ b₂) = sec₆ b₁ ⊔ sec₆ b₂
sec₆ (Less a b) = secₐ a ⊔ secₐ b

_≡_⦅≤_⦆ : state → state → level → Set
s₁ ≡ s₂ ⦅≤ l ⦆ = ∀ x → sec x ≤ l → s₁ x ≡ s₂ x

_≡_⦅<_⦆ : state → state → level → Set
s₁ ≡ s₂ ⦅< l ⦆ = ∀ x → sec x < l → s₁ x ≡ s₂ x

non-interference-aexp : ∀ a {s₁ s₂ l}
  → s₁ ≡ s₂ ⦅≤ l ⦆
  → secₐ a ≤ l
  → aval a s₁ ≡ aval a s₂
non-interference-aexp (N x) r e = refl
non-interference-aexp (V x) r e = r x e
non-interference-aexp (Plus a b) r e =
  cong₂ (_+_) (non-interference-aexp a r (m⊔n≤o⇒m≤o _ _ e))
              (non-interference-aexp b r (m⊔n≤o⇒n≤o _ _ e))

non-interference-bexp : ∀ a {s₁ s₂ l}
  → s₁ ≡ s₂ ⦅≤ l ⦆
  → sec₆ a ≤ l
  → bval a s₁ ≡ bval a s₂
non-interference-bexp (Bc x) r e = refl
non-interference-bexp (Not a) r e = cong not (non-interference-bexp a r e)
non-interference-bexp (And a b) r e =
  cong₂ (_∧_) (non-interference-bexp a r (m⊔n≤o⇒m≤o _ _ e))
              (non-interference-bexp b r (m⊔n≤o⇒n≤o _ _ e))
non-interference-bexp (Less a b) r e =
  cong₂ (_≤?_) (non-interference-aexp a r (m⊔n≤o⇒m≤o _ _ e))
               (non-interference-aexp b r (m⊔n≤o⇒n≤o _ _ e))

data _⊢_ : level → com → Set where
  SecSkip : ∀{l}
     → l ⊢ SKIP
  SecLoc : ∀{l a x}
     → secₐ a ≤ sec x
     → l ≤ sec x
     → l ⊢ (x ::= a)
  SecSeq : ∀{l c₁ c₂}
     → l ⊢ c₁
     → l ⊢ c₂
     → l ⊢ (c₁ :: c₂)
  SecIf : ∀{b l c₁ c₂}
     → (l ⊔ sec₆ b) ⊢ c₁
     → (l ⊔ sec₆ b) ⊢ c₂
     → l ⊢ (IF b THEN c₁ ELSE c₂)
  SecWhile : ∀{b l c}
     → (l ⊔ sec₆ b) ⊢ c
     → l ⊢ (WHILE b DO c)

anti-monotonicity : ∀{l l′ c}
  → l ⊢ c
  → l′ ≤ l
  → l′ ⊢ c
anti-monotonicity SecSkip s = SecSkip
anti-monotonicity (SecLoc x x₁) s = SecLoc x (≤-trans s x₁)
anti-monotonicity (SecSeq d d₁) s = SecSeq (anti-monotonicity d s) (anti-monotonicity d₁ s)
anti-monotonicity (SecIf d d₁) s = SecIf (anti-monotonicity d (⊔-monoˡ-≤ _ s)) (anti-monotonicity d₁ (⊔-monoˡ-≤ _ s))
anti-monotonicity (SecWhile d) s = SecWhile ((anti-monotonicity d (⊔-monoˡ-≤ _ s)))


data ⦅_,_⦆⇒_ : com → state → state → Set where
  Skip : ∀{s} → ⦅ SKIP , s ⦆⇒ s
  Loc : ∀{s x a}
         → ⦅ x ::= a , s ⦆⇒ (s [ x ::= aval a s ])
  Seq : ∀{c₁ c₂ s₁ s₂ s₃}
         → ⦅ c₁ , s₁ ⦆⇒ s₂
         → ⦅ c₂ , s₂ ⦆⇒ s₃
         → ⦅ c₁ :: c₂ , s₁ ⦆⇒ s₃
  IfTrue : ∀{c₁ c₂ b s t}
         → bval b s ≡ true
         → ⦅ c₁ , s ⦆⇒ t
         → ⦅ IF b THEN c₁ ELSE c₂ , s ⦆⇒ t
  IfFalse : ∀{c₁ c₂ b s t}
         → bval b s ≡ false
         → ⦅ c₂ , s ⦆⇒ t
         → ⦅ IF b THEN c₁ ELSE c₂ , s ⦆⇒ t
  WhileFalse : ∀{c b s}
         → bval b s ≡ false
         → ⦅ WHILE b DO c , s ⦆⇒ s
  WhileTrue : ∀{c b s₁ s₂ s₃}
         → bval b s₁ ≡ true
         → ⦅ c , s₁ ⦆⇒ s₂
         → ⦅ WHILE b DO c , s₂ ⦆⇒ s₃
         → ⦅ WHILE b DO c , s₁ ⦆⇒ s₃

confinement : ∀{c s t l}
  → ⦅ c , s ⦆⇒ t
  → l ⊢ c
  → s ≡ t ⦅< l ⦆
confinement Skip SecSkip x₂ x₃ = refl
confinement (Loc {x = x₂}) (SecLoc x x₁) e r with e ≟ x₂
... | yes refl = contradiction x₁ (<⇒≱ r)
... | no  _ = refl
confinement (Seq x x₄) (SecSeq x₁ x₅) x₂ x₃ =
  trans (confinement x x₁ x₂ x₃)
        (confinement x₄ x₅ x₂ x₃)
confinement (IfTrue x x₄) (SecIf x₁ x₅) x₂ x₃ = confinement x₄ x₁ x₂ (m<n⇒m<n⊔o _ x₃)
confinement (IfFalse x x₄) (SecIf x₁ x₅) x₂ x₃ = confinement x₄ x₅ x₂ (m<n⇒m<n⊔o _ x₃)
confinement (WhileFalse x) (SecWhile x₁) x₂ x₃ = refl
confinement {l = l} (WhileTrue x x₄ x₅) (SecWhile x₁) x₂ x₃ =
   trans (confinement x₄ (anti-monotonicity x₁ (m≤m⊔n _ _)) x₂ x₃)
         (confinement x₅ (SecWhile x₁) x₂ x₃)


true≢false : ¬ (true ≡ false)
true≢false = λ ()


reversal₁ : ∀{b c s₁ s₃}
  → ⦅ WHILE b DO c , s₁ ⦆⇒ s₃
  → bval b s₁ ≡ true
  → ∃[ s₂ ] ( ⦅ c , s₁ ⦆⇒ s₂ × ⦅ WHILE b DO c , s₂ ⦆⇒ s₃)
reversal₁ (WhileFalse x) v = contradiction (trans (sym v) x) true≢false
reversal₁ (WhileTrue x e e₁) v = -, e , e₁

reversal₂ : ∀{b c s₁ s₃}
  → ⦅ WHILE b DO c , s₁ ⦆⇒ s₃
  → bval b s₁ ≡ false
  → s₁ ≡ s₃
reversal₂ (WhileFalse x) v = refl
reversal₂ (WhileTrue x r r₁) v = contradiction (trans (sym x) v) true≢false

level-cong : ∀{l l′ c} → l ≡ l′ → l ⊢ c → l′ ⊢ c
level-cong refl x = x

≤⇒<suc : ∀{a b} → a ≤ b → a < suc b
≤⇒<suc z≤n = s≤s z≤n
≤⇒<suc (s≤s r) = s≤s (≤⇒<suc r)

non-interference : ∀{c s s′ t t′ l}
  → ⦅ c , s ⦆⇒ s′
  → ⦅ c , t ⦆⇒ t′
  → 0 ⊢ c
  → s  ≡ t  ⦅≤ l ⦆
  → s′ ≡ t′ ⦅≤ l ⦆
non-interference Skip Skip z e = e
non-interference (Loc {x = x₂} {a}) Loc (SecLoc x₃ z≤n) e x x₁ with x ≟ x₂
... | yes refl = non-interference-aexp a e (≤-trans x₃ x₁)
... | no _ = e x x₁
non-interference (Seq x cs) (Seq y ct) (SecSeq z z₁) e =
  non-interference cs ct z₁ (non-interference x y z e)
non-interference {l = l} (IfTrue {b = b} x cs) (IfTrue x₁ red) (SecIf w w₁) e r r₁ =
  non-interference cs red (anti-monotonicity w z≤n) e r r₁
non-interference {l = l} (IfTrue {b = b} x cs) (IfFalse x₁ red) (SecIf w w₁) e r r₁ =
  [ (λ secb≤l →
        let wr = non-interference-bexp b e secb≤l
         in contradiction (trans (sym x) (trans wr x₁)) true≢false)
  , (λ l<secb → let oo₁ = confinement cs w
                    oo₂ = confinement red w₁
                 in trans (sym (oo₁ r (<-transʳ r₁ l<secb)))
                   (trans (e r r₁)
                          (oo₂ r (<-transʳ r₁ l<secb))))
  ]  (≤-<-connex (sec₆ b) l)
non-interference {l = l} (IfFalse x₁ red) (IfTrue {b = b} x cs) (SecIf w w₁) e r r₁ =
  [ (λ secb≤l →
        let wr = non-interference-bexp b e secb≤l
         in contradiction (trans (sym x) (trans (sym wr) x₁)) true≢false)
  , (λ l<secb → let oo₁ = confinement cs w
                    oo₂ = confinement red w₁
                 in trans (sym (oo₂ r (<-transʳ r₁ l<secb)))
                   (trans (e r r₁)
                          (oo₁ r (<-transʳ r₁ l<secb))))
  ]  (≤-<-connex (sec₆ b) l)
non-interference (IfFalse x₁ red) (IfFalse x cs) (SecIf x₇ x₈) =
  non-interference red cs (anti-monotonicity x₈ z≤n)
non-interference (WhileFalse x) (WhileFalse x₁) (SecWhile z) e = e
non-interference {l = l} (WhileFalse {b = b} r) (WhileTrue c ct ct₁) (SecWhile z) e x x₁ =
  [ (λ secb≤l →
        let wr = non-interference-bexp b e secb≤l
         in contradiction (trans (sym c) (trans (sym wr) r)) true≢false)
  , (λ l<secb →
        let simp = confinement ct z
            simp2 = confinement ct₁ (SecWhile (level-cong (sym (m≤n⇒m⊔n≡n l<secb)) z))
         in trans (e x x₁) (trans (simp x (<-transʳ x₁ l<secb)) (simp2 x (≤⇒<suc x₁))))
  ]  (≤-<-connex (sec₆ b) l)
non-interference {l = l} (WhileTrue c ct ct₁) (WhileFalse {b = b} r) (SecWhile z) e x x₁ =
  [ (λ secb≤l →
        let wr = non-interference-bexp b e secb≤l
         in contradiction (trans (sym c) (trans wr r)) true≢false)
  , (λ l<secb →
        let simp = confinement ct z
            simp2 = confinement ct₁ (SecWhile (level-cong (sym (m≤n⇒m⊔n≡n l<secb)) z))
         in trans (trans (sym (simp2 x (≤⇒<suc x₁))) (sym (simp x ((<-transʳ x₁ l<secb))))) (e x x₁))
  ]  (≤-<-connex (sec₆ b) l)
non-interference {l = l} (WhileTrue {b = b} r cs cs₁) (WhileTrue c ct ct₁) (SecWhile z) e =
  let h₁ = non-interference cs ct (anti-monotonicity z z≤n) e
      h₂ = non-interference cs₁ ct₁ (SecWhile z) h₁
   in h₂
