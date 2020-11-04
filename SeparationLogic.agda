open import Data.Nat    using (ℕ; _+_) renaming (_≤?_ to _≤?ₙ_)
open import Data.Bool   using (Bool; true; false; not; _∧_)
open import Data.String using (String)
open import Data.Sum    using (_⊎_; [_,_]; inj₁; inj₂)
open import Relation.Binary using (Decidable)
open import Relation.Nullary           using (yes; no; ¬_)
open import Relation.Nullary.Negation  using (contradiction)
open import Data.List                  using (List; []; _∷_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Empty                 using (⊥-elim)
open import Data.Product               using (_×_; -,_; _-,-_; ∃; ∃-syntax) renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Level using (Level; suc; _⊔_)
open import Agda.Builtin.Sigma hiding (_,_) -- renaming (_,_ to _,,_)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
import Relation.Binary.PropositionalEquality as Eq

open import IMP hiding (com; state) ---using (aexp; aval; bexp; bval)

postulate
  _≟_ : Decidable {A = ℕ} _≡_

addr = ℕ

heap = addr → Maybe val

store = vname → val

state = store × heap

assn : ∀{l} → Set (suc l)
assn {a} = store → heap → Set a

emp : assn
emp _ h = ∀ a → h a ≡ nothing

_⊢>_ : IMP.aexp → IMP.aexp → assn
_⊢>_ a a′ s h = h (aval a s) ≡ just (aval a′ s)
              × ∀ (a″) → ¬(a″ ≡ aval a s) → h a″ ≡ nothing

_⊆_ : heap → heap → Set
h₀ ⊆ h = ∀ a → (h a ≡ nothing → h₀ a ≡ nothing)
             × (∀{o} → h₀ a ≡ just o → h₀ a ≡ h a)

heap-union : heap → heap → heap → addr → Set
heap-union h h₁ h₂ a with h a
... | just o = (h₁ a ≡ just o  × h₂ a ≡ nothing)
             ⊎ (h₁ a ≡ nothing × h₂ a ≡ just o)
... | nothing = h₁ a ≡ nothing × h₂ a ≡ nothing

_∼_⊥_ :  heap → heap → heap → Set
h ∼ h₁ ⊥ h₂ = ∀ a → heap-union h h₁ h₂ a

union-subset : ∀ h {h₁ h₂}
  → h ∼ h₁ ⊥ h₂
  → h₁ ⊆ h
union-subset h x a with h a  | x a
union-subset h x a | just x₁ | inj₁ (fst₁ ,, snd₁) = (λ ()) ,, (λ {x} x₁ → fst₁)
union-subset h x a | just x₁ | inj₂ (fst₁ ,, snd₁) rewrite fst₁ = (λ _ → refl) ,, (λ {x} ())
union-subset h x a | nothing | fst₁ ,, snd₁ = (λ x → fst₁) ,, (λ {x} x₁ → fst₁)

_*_ : ∀{l} → assn {l} → assn {l} → assn {l}
_*_ P Q s h = ∃[ h₁ ] ∃[ h₂ ] ((h ∼ h₁ ⊥ h₂)
                              × P s h₁
                              × Q s h₂)

_dom_ : addr → heap → Set
a dom h = ∃[ v ] (h a ≡ just v)

_¬dom_ : addr → heap → Set
a ¬dom h = h a ≡ nothing

_[_::=ₕ_] : heap → addr → val → heap
(h [ X ::=ₕ n ]) Y with Y ≟ X
... | yes _ = just n
... | no  _ = h Y

_/[_] : heap → addr → heap
(h /[ X ]) Y with Y ≟ X
... | yes _ = nothing
... | no  _ = h Y

data com : Set where
  SKIP  : com
  _::=_ : String → aexp → com
  _::_  : com  → com  → com 
  IF_THEN_ELSE_ : bexp → com  → com  → com
  WHILE_DO_     : bexp → com  → com
  _::=cons_     : String → addr → com
  _::=[_]  : String → aexp → com
  [_]::=_  : aexp → aexp → com
  dispose_ : aexp → com

data ⊢[_]_[_] {l} : assn {l} → com → assn {l} → Set (suc l) where
  Skip : ∀{P}
    → ⊢[ P ] SKIP [ P ]
  Loc : ∀{Q a x}
    → ⊢[ (λ s → Q (s [ x ::= aval a s ])) ] (x ::= a) [ Q ]
  Comp : ∀{P Q R c₁ c₂}
    → ⊢[ P ] c₁ [ Q ]
    → ⊢[ Q ] c₂ [ R ]
    → ⊢[ P ] c₁ :: c₂ [ R ]
  If : ∀{P b c₁ Q c₂}
    → ⊢[ (λ s h → P s h × bval b s ≡ true)  ] c₁ [ Q ]
    → ⊢[ (λ s h → P s h × bval b s ≡ false) ] c₂ [ Q ]
    → ⊢[ P ] (IF b THEN c₁ ELSE c₂) [ Q ]
  While : ∀{P b c}
    → ⊢[ (λ s h → P s h × bval b s ≡ true) ] c [ P ]
    → ⊢[ P ] (WHILE b DO c) [ (λ s h → P s h × bval b s ≡ false) ]
  Conseq : ∀{P Q P′ Q′ : assn} {c}
    → (∀ s h → P′ s h → P s h)
    → ⊢[ P  ] c [ Q  ]
    → (∀ s h → Q s h → Q′ s h)
    → ⊢[ P′ ] c [ Q′ ]
  Frame : ∀{A B R c}
    → ⊢[ A     ] c [ B     ]
    → ⊢[ A * R ] c [ B * R ]

data config : Set where
  ⦅_,_,_⦆ : com → store → heap → config
  abort  : config

data _⇒_ : config → config → Set where
  Loc : ∀{x a s h}
      → ⦅ x ::= a , s , h ⦆ ⇒ ⦅ SKIP , (s [ x ::= aval a s ]) , h ⦆
  Comp₁ : ∀{c s h}
      → ⦅ SKIP :: c , s , h ⦆ ⇒ ⦅ c , s , h ⦆
  Comp₂ : ∀{c₁ c₁′ c₂ s s′ h h′}
      → ⦅ c₁       , s , h ⦆ ⇒ ⦅ c₁′       , s′ , h′ ⦆
      → ⦅ c₁ :: c₂ , s , h ⦆ ⇒ ⦅ c₁′ :: c₂ , s′ , h′  ⦆
  CompFail : ∀{c₁ c₂ s h}
      → ⦅ c₁       , s , h ⦆ ⇒ abort
      → ⦅ c₁ :: c₂ , s , h ⦆ ⇒ abort
  IfTrue  : ∀{b s c₁ c₂ h}
      → bval b s ≡ true
      → ⦅ IF b THEN c₁ ELSE c₂ , s , h ⦆ ⇒ ⦅ c₁ , s , h ⦆
  IfFalse : ∀{b s c₁ c₂ h}
      → bval b s ≡ false
      → ⦅ IF b THEN c₁ ELSE c₂ , s , h ⦆ ⇒ ⦅ c₂ , s , h ⦆           
  While : ∀{b s c h}
      → ⦅ WHILE b DO c , s , h ⦆ ⇒ ⦅ IF b THEN (c :: (WHILE b DO c)) ELSE SKIP , s , h ⦆
  Cons : ∀{l h s x h′ s′}
      → l ¬dom h
      → h′ ≡ h [ l ::=ₕ 0 ]
      → s′ ≡ s [ x ::= l  ] 
      → ⦅ x ::=cons l , s , h ⦆ ⇒ ⦅ SKIP , s′ , h′ ⦆
  Lookup : ∀{a s x h v s′}
      → (aval a s) dom h
      → s′ ≡ s [ x ::= v ]
      → ⦅ x ::=[ a ] , s , h ⦆ ⇒ ⦅ SKIP , s′ , h  ⦆
  LookupFail : ∀{a s x h}
      → (aval a s) ¬dom h
      → ⦅ x ::=[ a ] , s , h ⦆ ⇒ abort
  Write : ∀{a s a′ h}
      → (aval a s) dom h
      → ⦅ [ a ]::= a′ , s , h ⦆ ⇒ ⦅ SKIP , s , h [ aval a s ::=ₕ aval a′ s ]  ⦆
  WriteFail : ∀{a s a′ x h}
      → (aval a s) ¬dom h
      → ⦅ [ x ]::= a′ , s , h ⦆ ⇒ abort
  Dispose : ∀{a s h}
      → (aval a s) dom h
      → ⦅ dispose a , s , h ⦆ ⇒ ⦅ SKIP , s , h /[ aval a s ]  ⦆
  DisposeFail : ∀{a s h}
      → (aval a s) ¬dom h
      → ⦅ dispose a , s , h ⦆ ⇒ abort

data _⇒*_ : config → config → Set where
  _∎ : ∀ c → c ⇒* c
  _→⟨_⟩_ : ∀ c {c′ c″}
         → c  ⇒  c′
         → c′ ⇒* c″
         → c  ⇒* c″ 

Safe : config → Set
Safe c = ¬ (c ⇒* abort)

lemma1 : ∀{c s h₀ h}
       → h₀ ⊆ h
       → ⦅ c , s , h  ⦆ ⇒ abort
       → ⦅ c , s , h₀ ⦆ ⇒ abort
lemma1 sub (CompFail r) = CompFail (lemma1 sub r)
lemma1 sub (LookupFail {a}{s} r) = LookupFail (fst (sub (aval a s)) r)
lemma1 sub (WriteFail {a}{s} r) = WriteFail {a} (fst (sub (aval a s)) r)
lemma1 sub (DisposeFail {a}{s} r) = DisposeFail (fst (sub (aval a s)) r)

subset-update : ∀ l {h h₀ v}
  →  h₀ ⊆ h
  → (h₀ [ l ::=ₕ v ]) ⊆ (h [ l ::=ₕ v ])
subset-update l b Y with Y ≟ l
... | yes p = (λ x → x) ,, λ {o} _ → refl
... | no ¬p = b Y

subset-delete : ∀ v {h h₀}
  →  h₀ ⊆ h
  → (h₀ /[ v ]) ⊆ (h /[ v ])
subset-delete l b Y with Y ≟ l
... | yes p = (λ x → refl) ,, (λ {x} x₁ → refl)
... | no ¬p = b Y

lemma2 : ∀ h₀ {h c c′ s s′ h′}
       → h₀ ⊆ h
       → ⦅ c , s , h  ⦆ ⇒ ⦅ c′ , s′ , h′ ⦆
       → ⦅ c , s , h₀ ⦆ ⇒ abort
       ⊎ (∃[ h′₀ ] (h′₀ ⊆ h′
       × ⦅ c , s , h₀ ⦆ ⇒ ⦅ c′ , s′ , h′₀ ⦆))
lemma2 h₀ x Loc = inj₂ (h₀ ,, x ,, Loc)
lemma2 h₀ x Comp₁ = inj₂ (h₀ ,, x ,, Comp₁)
lemma2 h₀ x (Comp₂ x₁) with lemma2 h₀ x x₁
lemma2 h₀ x (Comp₂ x₁) | inj₁ x₂ = inj₁ (CompFail x₂)
lemma2 h₀ x (Comp₂ x₁) | inj₂ (h′₀ ,, sub ,, red) = inj₂ (h′₀ ,, sub ,, Comp₂ red)
lemma2 h₀ x (IfTrue x₁) = inj₂ (h₀ ,, x ,, IfTrue x₁)
lemma2 h₀ x (IfFalse x₁)  = inj₂ (h₀ ,, x ,, IfFalse x₁)
lemma2 h₀ x While         = inj₂ (h₀ ,, x ,, While)
lemma2 h₀ x (Cons {l} x₁ A B) rewrite A | B = inj₂ ( (h₀ [ l ::=ₕ 0 ])
                                            ,, subset-update l x
                                            ,, Cons (fst (x l) x₁) refl refl)
lemma2 h₀ x (Lookup {a}{s} (_ ,, p) A) rewrite A with h₀ (aval a s) | Eq.inspect h₀ (aval a s)
... | nothing | Eq.[ eq ] = inj₁ (LookupFail eq)
... | just o  | Eq.[ eq ] = inj₂ ( h₀
                                ,, x
                                ,, Lookup (-, Eq.trans (snd (x (aval a s)) eq) p) refl)
lemma2 h₀ x (Write {a}{s}{a′} (_ ,, x₁)) with h₀ (aval a s) | Eq.inspect h₀ (aval a s)
... | nothing | Eq.[ eq ] = inj₁ (WriteFail {a} eq)
... | just o  | Eq.[ eq ] = inj₂ ( (h₀ [ aval a s ::=ₕ aval a′ s ])
                                ,, subset-update (aval a s) x
                                ,, Write (-, (Eq.trans (snd (x (aval a s)) eq) x₁)))
lemma2 h₀ x (Dispose {a}{s} (_ ,, x₁)) with h₀ (aval a s) | Eq.inspect h₀ (aval a s)
... | nothing | Eq.[ eq ] = inj₁ (DisposeFail eq)
... | just o  | Eq.[ eq ] = inj₂ ( (h₀ /[ aval a s ])
                                ,, subset-delete (aval a s) x
                                ,, Dispose (-, (Eq.trans (snd (x (aval a s)) eq) x₁)))

frame1sub : ∀{c s h H}
  → h ⊆ H
  → Safe ⦅ c , s , h ⦆
  → Safe ⦅ c , s , H ⦆
frame1sub {c}{s}{h}{H} x x₁ (_→⟨_⟩_ .(⦅ c , s , H ⦆) {⦅ x₄ , x₅ , x₆ ⦆} x₂ x₃) with lemma2 h x x₂
... | inj₁ x₇ = x₁ (⦅ c , s , h ⦆ →⟨ x₇ ⟩ (abort ∎))
... | inj₂ (_ ,, fst₂ ,, snd₁) = frame1sub fst₂ (λ z → x₁ (_ →⟨ snd₁ ⟩ z)) x₃
frame1sub {c}{s}{h}{H} x x₁ (_→⟨_⟩_ .(⦅ c , s , H ⦆) {abort} x₂ x₃) = x₁ (_ →⟨ lemma1 x x₂ ⟩ (abort ∎))

frame1 : ∀{c s h H z}
  → H ∼ h ⊥ z
  → Safe ⦅ c , s , h ⦆
  → Safe ⦅ c , s , H ⦆
frame1 {H = H} x x₁ x₂ = frame1sub (union-subset H x) x₁ x₂

heap-union-update : ∀{l h h₀ h₁ v}
  → l ¬dom h₁
  →  h               ∼  h₀               ⊥ h₁
  → (h [ l ::=ₕ v ]) ∼ (h₀ [ l ::=ₕ v ]) ⊥ h₁
heap-union-update {l}{h}{v = v} d x a with (h [ l ::=ₕ v ]) a | Eq.inspect (h [ l ::=ₕ v ]) a
heap-union-update {l}{h} d x a | just x₁ | Eq.[ eq ] with a ≟ l | h a | Eq.inspect h a | x a
heap-union-update {l}{h} d x a | just x₁ | Eq.[ eq ] | yes p | just x₂ | Eq.[ eq2 ] | inj₁ x₃ = inj₁ (eq ,, snd x₃)
heap-union-update {l}{h} d x a | just x₁ | Eq.[ eq ] | yes p | just x₂ | Eq.[ eq2 ] | inj₂ y rewrite p = inj₁ (eq ,, d)
heap-union-update {l}{h} d x a | just x₁ | Eq.[ eq ] | yes p | nothing | Eq.[ eq2 ] | C = inj₁ (eq ,, snd C)
heap-union-update {l}{h} d x a | just x₁ | Eq.[ eq ] | no ¬p | just x₂ | Eq.[ eq2 ] | inj₁ x₃ rewrite (Eq.trans (sym eq) eq2) = inj₁ x₃
heap-union-update {l}{h} d x a | just x₁ | Eq.[ eq ] | no ¬p | just x₂ | Eq.[ eq2 ] | inj₂ y  rewrite (Eq.trans (sym eq) eq2) = inj₂ y
heap-union-update {l}{h} d x a | just x₁ | Eq.[ eq ] | no ¬p | nothing | Eq.[ eq2 ] | C       rewrite (Eq.trans (sym eq) eq2) = inj₁ C
heap-union-update {l}{h} d x a | nothing | Eq.[ eq ] with a ≟ l | h a | Eq.inspect h a | x a
heap-union-update {l}{h} d x a | nothing | Eq.[ eq ] | no ¬p | just x₁ | Eq.[ eq2 ] | inj₁ x₂ = Eq.trans (Eq.trans (fst x₂) (sym eq2)) eq ,, snd x₂
heap-union-update {l}{h} d x a | nothing | Eq.[ eq ] | no ¬p | just x₁ | Eq.[ eq2 ] | inj₂ y = fst y ,, Eq.trans (snd y) (Eq.trans (sym eq2) eq)
heap-union-update {l}{h} d x a | nothing | Eq.[ eq ] | no ¬p | nothing | Eq.[ eq2 ] | E = E

heap-union-delete : ∀{h h₀ h₁ v}
  → v ¬dom h₁
  → h          ∼  h₀         ⊥ h₁
  → (h /[ v ]) ∼ (h₀ /[ v ]) ⊥ h₁
heap-union-delete {h}{h₀}{h₁}{v} d x a with (h /[ v ]) a | Eq.inspect (h /[ v ]) a
heap-union-delete {h} {h₀} {h₁} {v} d x a | just x₁ | Eq.[ eq ] with a ≟ v | h a | Eq.inspect h a | x a
heap-union-delete {h} {h₀} {h₁} {v} d x a | just x₁ | Eq.[ () ] | yes p | just x₂ | Eq.[ eq2 ] | R
heap-union-delete {h} {h₀} {h₁} {v} d x a | just x₁ | Eq.[ eq ] | no ¬p | just x₂ | Eq.[ eq2 ] | inj₁ x₃ rewrite (Eq.trans (sym eq) eq2) = inj₁ x₃
heap-union-delete {h} {h₀} {h₁} {v} d x a | just x₁ | Eq.[ eq ] | no ¬p | just x₂ | Eq.[ eq2 ] | inj₂ y  rewrite (Eq.trans (sym eq) eq2) = inj₂ y
heap-union-delete {h} {h₀} {h₁} {v} d x a | just x₁ | Eq.[ eq ] | no ¬p | nothing | Eq.[ eq2 ] | fst₁ ,, snd₁ = inj₂ (fst₁ ,, Eq.trans snd₁ (Eq.trans (sym eq2) eq))
heap-union-delete {h} {h₀} {h₁} {v} d x a | nothing | Eq.[ eq ] with a ≟ v | h a | Eq.inspect h a | x a
heap-union-delete {h} {h₀} {h₁} {v} d x a | nothing | Eq.[ eq ] | yes p | just x₁ | Eq.[ eq2 ] | inj₁ x₂ = refl ,, snd x₂
heap-union-delete {h} {h₀} {h₁} {v} d x a | nothing | Eq.[ eq ] | yes p | just x₁ | Eq.[ eq2 ] | inj₂ y rewrite p = refl ,, d
heap-union-delete {h} {h₀} {h₁} {v} d x a | nothing | Eq.[ eq ] | yes p | nothing | Eq.[ eq2 ] | E = refl ,, snd E
heap-union-delete {h} {h₀} {h₁} {v} d x a | nothing | Eq.[ eq ] | no ¬p | just x₁ | Eq.[ eq2 ] | inj₁ x₂ = Eq.trans (fst x₂) (Eq.trans (sym eq2) eq) ,, snd x₂
heap-union-delete {h} {h₀} {h₁} {v} d x a | nothing | Eq.[ eq ] | no ¬p | just x₁ | Eq.[ eq2 ] | inj₂ y = fst y ,, Eq.trans (snd y) (Eq.trans (sym eq2) eq)
heap-union-delete {h} {h₀} {h₁} {v} d x a | nothing | Eq.[ eq ] | no ¬p | nothing | Eq.[ eq2 ] | E = E

union-exclusionᵣ : ∀{l h h₀ h₁}
  → h ∼ h₀ ⊥ h₁
  → l ¬dom h
  → l ¬dom h₁
union-exclusionᵣ {l}{h} A B with h l | A l
... | nothing | fst₁ ,, snd₁ = snd₁


union-presenceᵣ : ∀{l h h₀ h₁}
  → h ∼ h₀ ⊥ h₁
  → l dom h
  → l dom h₀
  → l ¬dom h₁
union-presenceᵣ {l}{h} A B C with h l | A l
union-presenceᵣ {l} {h} A B C | just x | inj₁ (fst₁ ,, snd₁) = snd₁
union-presenceᵣ {l} {h} A B (fst₁ ,, snd₁) | just x | inj₂ (fst₂ ,, snd₂) with Eq.trans (sym fst₂) snd₁
... | ()


union-reduction : ∀{a b c s h′ h h₀ h′₀ h₁}
  → ⦅ c , s , h₀ ⦆ ⇒ ⦅ a , b , h′₀ ⦆
  → ⦅ c , s , h  ⦆ ⇒ ⦅ a , b , h′  ⦆
  → h  ∼ h₀  ⊥ h₁
  → h′ ∼ h′₀ ⊥ h₁
union-reduction Loc Loc C = C
union-reduction Comp₁ Comp₁ C = C
union-reduction (Comp₂ A) (Comp₂ B) C = union-reduction A B C
union-reduction (IfTrue x) (IfTrue x₁) C = C
union-reduction (IfTrue x) (IfFalse x₁) C = C
union-reduction (IfFalse x) (IfTrue x₁) C = C
union-reduction (IfFalse x) (IfFalse x₁) C = C
union-reduction While While C = C
union-reduction (Cons d A B) (Cons d2 A′ B′) C a rewrite A | B | A′ | B′ = heap-union-update (union-exclusionᵣ C d2) C a
union-reduction (Lookup e A) (Lookup e2 A′) C rewrite A | A′ = C
union-reduction (Write x) (Write x₁) C a = heap-union-update (union-presenceᵣ C x₁ x) C a
union-reduction (Dispose x) (Dispose x₁) C a = heap-union-delete (union-presenceᵣ C x₁ x) C a


frame2 : ∀{c s h h₀ h₁ h′ s′}
  → Safe ⦅ c , s , h₀ ⦆
  → h ∼ h₀ ⊥ h₁
  → ⦅ c , s , h ⦆ ⇒* ⦅ SKIP , s′ , h′ ⦆
  → ∃[ h′₀ ] ( ⦅ c , s , h₀ ⦆ ⇒* ⦅ SKIP , s′ , h′₀ ⦆
             × h′ ∼ h′₀ ⊥ h₁ )
frame2 s t (.(⦅ SKIP , _ , _ ⦆) ∎) = _ ,, (_ ∎) ,, t
frame2 {h₀ = h₀} s t (_→⟨_⟩_ .(⦅ _ , _ , _ ⦆) {⦅ _ , _ , _ ⦆} x r) with lemma2 h₀ (union-subset _ t) x
... | inj₁ x₄ = ⊥-elim (s (_ →⟨ x₄ ⟩ (abort ∎)))
... | inj₂ (fst₁ ,, fst₂ ,, snd₁) with frame2 (λ z → s (_ →⟨ snd₁ ⟩ z)) (union-reduction snd₁ x t) r
... | fst₃ ,, fst₄ ,, snd₂ = fst₃ ,, (_ →⟨ snd₁ ⟩ fst₄) ,, snd₂
frame2 s t (_→⟨_⟩_ .(⦅ _ , _ , _ ⦆) {abort} x (.abort →⟨ () ⟩ r))

⊨[_]_[_] : assn → com → assn → Set
⊨[ A ] c [ B ] = ∀{s h}
  → A s h
  → Safe ⦅ c , s , h ⦆
  × (∀{s′ h′} → ⦅ c , s , h ⦆ ⇒* ⦅ SKIP , s′ , h′ ⦆ → B s′ h′)

NotInfluenced : assn → com → Set
NotInfluenced R c = ∀{s s′ z h₀ h′₀ hᵣ}
  → z ∼ h′₀ ⊥ hᵣ
  → ⦅ c , s , h₀ ⦆ ⇒* ⦅ SKIP , s′ , h′₀ ⦆ 
  → R s hᵣ → R s′ hᵣ

frame-soundness : ∀{A B R : assn} {c}
  → NotInfluenced R c
  → ⊨[ A     ] c [ B     ]
  → ⊨[ A * R ] c [ B * R ]
frame-soundness {A}{B}{R}{c} Inf H {s}{h} (h₀ ,, h₁ ,, ⊥ ,, A₀ ,, R₁) with H A₀
... | safe ,, conv = frame1 ⊥ safe ,, frame2-ex
   where frame2-ex : ∀{s′ h′}
                   → ⦅ c , s , h ⦆ ⇒* ⦅ SKIP , s′ , h′ ⦆
                   → ∃[ h₁ ] ∃[ h₂ ] ( (h′ ∼ h₁ ⊥ h₂)
                                     × B s′ h₁
                                     × R s′ h₂)
         frame2-ex rs with frame2 safe ⊥ rs
         ... | h′₀ ,, r ,, ⊥′ = h′₀ ,, h₁ ,, ⊥′ ,, conv r  ,, Inf ⊥′ r R₁
