module Bottom where

open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.List as List using (_∷_ ; [] ; List ; sum )
open import Relation.Binary
open import Data.Nat as ℕ using (ℕ ; suc ; zero ; _≥_ ; _<_ ; _≥?_ ; _<?_ ; _∸_ ; pred)
open import Data.Fin using (Fin ; suc ; zero)
open import Data.List.Relation.Unary.Sorted.TotalOrder hiding (head)
open import Data.Product
open import Relation.Binary.PropositionalEquality as Eq
import Data.Fin.Properties as Fin
open import Function.Base
import Function
import Data.Nat.Properties as ℕ
open import Data.Nat.Induction
open import Relation.Nullary
open import Data.List.Relation.Unary.Linked hiding (head)
open import Induction
open import Induction.WellFounded as WF
open import Data.List.NonEmpty
open import Data.String as String using (String)
open import Data.Char as Char using (Char)
open import Data.List.Relation.Unary.All as All using (All ; _∷_ ; [])

private
  variable
    ℓ ℓ' : Level
    A B C : Set ℓ
    n m : ℕ


module _ (b₀ : ℕ) (P : ℕ → Set ℓ) (base : ∀ n → n < suc b₀ → P n) (step : ∀ n → P n → P (suc b₀ ℕ.+ n)) where

  private
    b = b₀

  wfStep : (n : ℕ) → (∀ m → m < n → P m) → P n
  wfStep n rec with ℕ.compare n b
  ... | ℕ.less .n k = base n (ℕ.s≤s (ℕ.≤-step (ℕ.m≤m+n n k)))
  ... | ℕ.equal .n = base n ℕ.≤-refl
  ... | ℕ.greater .b₀ k = step k (rec k (ℕ.s≤s (ℕ.m≤n+m k b₀)))

  +induction : ∀ x → P x
  +induction = <-rec P wfStep





data Emoji : Set where
  comma beg sparkle glitterheart hug : Emoji


value : Emoji → ℕ
value hug = 200
value glitterheart = 50
value sparkle = 10
value beg = 5
value comma = 1

character : Emoji → Char
character comma = '\x002C'
character beg = '\x1F97A' 
character sparkle = '\x2728'
character glitterheart = '\x1F496'
character hug = '\x1FAC2'

fromValue : ℕ → Emoji
fromValue n with n ℕ.≟ 200
... | yes _ = hug
... | no _ with n ℕ.≟ 50
... | yes _ = glitterheart
... | no _ with n ℕ.≟ 10
... | yes _ = sparkle
... | no _ with n ℕ.≟ 5
... | yes _ = beg
... | no _ = comma


Injective : (A → B) → Set _
Injective = Function.Injective _≡_ _≡_

Inverseˡ : (A → B) → (B → A) → Set _
Inverseˡ {A = A} {B = B} f g = Function.Inverseˡ {A = A} _≡_ _≡_ f g

Inverseʳ : (A → B) → (B → A) → Set _
Inverseʳ {A = A} {B = B} f g = Function.Inverseʳ {B = B} _≡_ _≡_ f g

invʳ→inj : {f : A → B} (g : B → A) → Inverseʳ f g → Injective f
invʳ→inj {f = f} g p {x} {y} q =
  x ≡⟨ sym (p x) ⟩
  g (f x) ≡⟨ cong g q ⟩
  g (f y) ≡⟨ p y ⟩
  y ∎ where open ≡-Reasoning

fromValue-value : Inverseʳ value fromValue
fromValue-value comma = refl
fromValue-value beg = refl
fromValue-value sparkle = refl
fromValue-value glitterheart = refl
fromValue-value hug = refl

value-injective : ∀ {x y} → value x ≡ value y → x ≡ y
value-injective = invʳ→inj fromValue fromValue-value


value-suc : ∀ {e} → value e ≡ suc (pred (value e))
value-suc {comma} = refl
value-suc {beg} = refl
value-suc {sparkle} = refl
value-suc {glitterheart} = refl
value-suc {hug} = refl


_≤_ : Emoji → Emoji → Set
_≤_ = ℕ._≤_ on value


≤-antisym : Antisymmetric _≡_ (ℕ._≥_ on value)
≤-antisym lt gt = value-injective (ℕ.≤-antisym gt lt)

isTotalOrder : IsTotalOrder _≡_ (ℕ._≥_ on value)
isTotalOrder = record
  { isPartialOrder = record
    { isPreorder = record
      { isEquivalence = Eq.isEquivalence
      ; reflexive = λ { refl → ℕ.≤-refl }
      ; trans = flip ℕ.≤-trans
      }
    ; antisym = ≤-antisym
    }
  ; total = λ _ _ → ℕ.≤-total _ _
  }

Emoji-Order : TotalOrder _ _ _
Emoji-Order = record
  { Carrier = Emoji
  ; _≈_ = _≡_
  ; _≤_ = ℕ._≥_ on value
  ; isTotalOrder = isTotalOrder
  }

record Group⁺ : Set where
  constructor mkGrp
  field
    emoji⁺ : List⁺ Emoji

  emoji = toList emoji⁺

  field

    @0 sorted : Sorted Emoji-Order emoji

record HasRep⁺ (n : ℕ) : Set where
  constructor mkRep
  field
    group⁺ : Group⁺
    sum-≡ : sum (List.map value (Group⁺.emoji group⁺)) ≡ n

record HasRep⁺_at_ (n : ℕ) (@0 e : Emoji) : Set where
  constructor mkRepAt
  field
    rep : HasRep⁺ n
    @0 head≤ : head (Group⁺.emoji⁺ (HasRep⁺.group⁺ rep)) ≤ e


Rep-at-weaken : ∀ {n e e'} → (@0 _ : e ≤ e') → HasRep⁺ n at e → HasRep⁺ n at e'
Rep-at-weaken p (mkRepAt reps head≤) = mkRepAt reps (ℕ.≤-trans head≤ p)

data HasRep : ℕ → Set where
  group : HasRep⁺ n → HasRep n
  heart : HasRep 0

toEmoji⁺-at : ∀ e n → (∀ m → m < value e → HasRep⁺ (suc m) at e) → HasRep⁺ (suc n) at e
toEmoji⁺-at e n base = +induction
  (pred (value e))
  (λ n → HasRep⁺ (suc n) at e)
  (λ n p → base n (subst (n <_) (sym value-suc) p))
  (λ n p → subst (λ k → HasRep⁺ k at e) (trans (ℕ.+-suc _ _) (cong (λ k → suc (k ℕ.+ n)) value-suc)) (step (suc n) p))
  n
  where
  step : ∀ k → HasRep⁺ k at e → HasRep⁺ (value e ℕ.+ k) at e
  step ._ (mkRepAt (mkRep (mkGrp emoji⁺ sorted) refl) head≤) = mkRepAt (mkRep (mkGrp (e ∷⁺ emoji⁺) (head≤ ∷ sorted)) refl) ℕ.≤-refl


toEmoji⁺ : ∀ n → HasRep⁺ (suc n)
toEmoji⁺ n = HasRep⁺_at_.rep rep where
  rep : HasRep⁺ (suc n) at hug
  rep = toEmoji⁺-at hug n
    λ m lt → Rep-at-weaken (ℕ.m≤m*n 50 {4} (ℕ.s≤s ℕ.z≤n)) $ toEmoji⁺-at glitterheart m
      λ m lt → Rep-at-weaken (ℕ.m≤m*n 10 {5} (ℕ.s≤s ℕ.z≤n)) $ toEmoji⁺-at sparkle m
        λ m lt → Rep-at-weaken (ℕ.m≤m*n 5 {2} (ℕ.s≤s ℕ.z≤n)) $ toEmoji⁺-at beg m
          λ m lt → Rep-at-weaken (ℕ.s≤s ℕ.z≤n) $ toEmoji⁺-at comma m
            λ { .zero (ℕ.s≤s ℕ.z≤n) → mkRepAt (mkRep (mkGrp (comma ∷ []) [-]) refl) (ℕ.s≤s ℕ.z≤n) }


toEmoji : ∀ n → HasRep n
toEmoji zero = heart
toEmoji (suc n) = group (toEmoji⁺ n)

emjToString' : HasRep n → String
emjToString' heart = "\x2764\xFE0F"
emjToString' (group (mkRep group⁺ sum-≡)) = String.fromList (List.map character (Group⁺.emoji group⁺))

emjToString : HasRep n → String
emjToString rep = emjToString' rep String.++ "\x1F449\x1F448"
