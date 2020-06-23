open import Data.Nat     using (ℕ; suc; zero; _<_; _≤_; z≤n; s≤s; _+_; _⊔_)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; <-transˡ; <-transʳ; ≤-total)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)
open import Relation.Nullary using (¬_)
open import Data.Sum using (inj₁; inj₂; _⊎_; [_,_])

contra : ∀ {a l} → suc a ≤ l → ¬ (l ≤ a)
contra {l = suc l} (s≤s a) (s≤s f) = contra a f

base : ∀(a b) → (a ≤ b) ⊎ (b < a)
base zero b = inj₁ z≤n
base (suc a) (zero) = inj₂ (s≤s z≤n)
base (suc a) (suc b) with base (a) (b)
... | inj₁ x = inj₁ (s≤s x)
... | inj₂ y = inj₂ (s≤s y)

missing : ∀ {a b} → a ≤ b → a < suc b
missing r = s≤s r

dam : ∀ (a b) → a ≤ b → a ≡ b ⊎ a < b
dam .0 zero z≤n = inj₁ refl
dam .0 (suc b) z≤n = inj₂ (s≤s z≤n)
dam .(suc m) .(suc n) (s≤s {m} {n} r) with dam m n r
dam .(suc m) .(suc n) (s≤s {m} {n} r) | inj₁ x = inj₁ (cong suc x)
dam .(suc m) .(suc n) (s≤s {m} {n} r) | inj₂ y = inj₂ (s≤s y)
