# CoEndoYoneda Equivalence and Purity

```agda
module CoEndoYonedaEquivalenceAndPurity where
```

## Equivalence

### Set levels

First we need to `import` some set level library artifacts, `Level` in general and `_⊔_` in
particular.

```agda
open import Level using (Level; _⊔_)
```

Set levels are one of the more challenging aspects of proof assistants in general and `Agda` in
particular.

They are, among others, introduced to avoid paradoxes like Russel's paradox :
"the set of all sets is not a set".

So, yes, you will, from time to time, be confronted with some "set level mumbo-jumbo" but, frankly,
in this document, the set level impact is very limited.

We need function composition, `_•_`, and function identity, `idf`. We are `renaming` in order to
disambigate them from morphism composition and morphism identity.

```agda
open import Function.Base renaming (_∘_ to _•_; id to idf)
```

We need the propositional binary equality relation, `_≡_`.

```agda
open import Relation.Binary.PropositionalEquality using (_≡_)
```

We encode equivalence as two functions, `from` and `to`, that are each other's inverses.

```agda
record _⇿_ {ℓ ℓ' : Level} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  field
    to : A → B
    from : B → A
    to_from : to • from ≡ idf
    from_to : from • to ≡ idf
```

To start with, we set the scene by encoding the standard coEndoYoneda equivalence.

We need the category of sets instance, `Sets` , functors, `Functor` and natural transformations,
`NaturalTransformation`. 

It is convenient to `open` both `Functor` and `NaturalTransformation`.

```agda
open import Categories.Category.Instance.Sets using (Sets)

open import Categories.Functor.Core using (Functor)

open import Categories.NaturalTransformation.Core using (NaturalTransformation)

open Functor
open NaturalTransformation
```

We need definitional equality, `refl`, symmetry of equality, `sym`, and propositional
extensionality `Extensionality`.

`Extensionality` extends propositions of values to functions.

`Extensionality` is introduced as a `postulate` named `funext`.

```agda
open import Relation.Binary.PropositionalEquality using (refl; sym)
open import Axiom.Extensionality.Propositional using (Extensionality)

postulate
  funext : ∀ {a b} → Extensionality a b
```

The standard coEndoYoneda equivalence has a set level that is one level higher than the set level
it is an equivalence about.

We need another set level library artifact, `suc`.

```agda
open import Level using (suc)
```

The standard coEndoYoneda equivalence is about the endofunctor, `Sets_CYEF`, of the category of
sets, `Sets ℓ`, that, given an object, i.e. a set, `X : Set ℓ`, at object level, maps every object,
i.e. set, `Y : Set ℓ` to all morphisms, i.e. functions, `X → Y` from `X` to `Y`, and, at morphism
level, maps every morphism, i.e. function, `f : Y → Z` to composing it with all morphisms, i.e.
functions, `g : X → Y` obtaining morphisms, i.e. functions, `f • g : X → Z`.

The standard coEndoYoneda equivalence also comes with functor law proofs.

```agda
variable ℓ : Level

record StandardCoEndoYonedaEquivalence : Set (suc ℓ) where

  Sets_CYEF : Set ℓ → Functor (Sets ℓ) (Sets ℓ)
  Sets_CYEF X = record
    { F₀ = λ Y → X → Y
    ; F₁ = λ f g → f • g
    ; identity = λ {Y} g → refl
    ; homomorphism = λ {Y Z W f h} g → refl 
    ; F-resp-≈ = λ f≈h g → funext (λ x → f≈h (g x))
    }
```

Given an endofunctor, `F : Functor (Sets ℓ) (Sets ℓ)`, of the category of sets, `Sets ℓ`, and an
object `X`, the standard coEndoYoneda equivalence is an quivalence between, on the one hand,
natural transformations, `NaturalTransformation (Sets_CYEF X) F`, from `Sets_CYEF X` to `F` and,
on the other hand, elements of the set `(F₀ F) X`. Recall that we are dealing with the category of
sets.

This equivalence is the foundation of studying sets, `X`, by studying all functions, `X → Y`, from
it to sets `Y`.

The definition of `τx2fx` is simple (I did not write it is easy) : given a natural transformation
`τx`, apply `η τx X` to `idf`.

The `η` definition of `fx2τx` in terms of `fx2τx-η` is also simple (I did not write it is easy) :
given an element `fx` of `(F₀ F) X`, a set `Y` and a function `f : X → Y`, apply `F1 F` to `f` and
apply the obtained function, `(F₁ F) f : (F₀ F) X → (F₀ F) Y` to `fx`. But the complete definition
of `fx2τx` is more complex because it also involves the natural transformation law proof. Again,
the proof is simple (I did not write it is easy). It uses the `homomorphism` functor law.

The `equivalence` definition uses a `postulate` about natural transformations that is similar to
the extensionality postulate about functions.

```agda
  module StandardEquivalence 
    (F : Functor (Sets ℓ) (Sets ℓ))
    (X : Set ℓ) where

    open Relation.Binary.PropositionalEquality.≡-Reasoning

    τx2fx : NaturalTransformation (Sets_CYEF X) F → (F₀ F) X
    τx2fx τx = η τx X idf

    fx2τx-η : (F₀ F) X → ∀ Y → (F₀ (Sets_CYEF X) Y → (F₀ F) Y)
    fx2τx-η fx Y f = (F₁ F) f fx

    fx2τx-commute : ∀ (fx : (F₀ F) X) {Y Z : Set ℓ} (f : Y → Z) (g : (F₀ (Sets_CYEF X)) Y) → 
      fx2τx-η fx Z (F₁ (Sets_CYEF X) f g) ≡ (F₁ F f) (fx2τx-η fx Y g)
    fx2τx-commute fx {Y} {Z} f g = begin
      fx2τx-η fx Z (F₁ (Sets_CYEF X) f g)
        ≡⟨ refl ⟩
      fx2τx-η fx Z (f • g)
        ≡⟨ refl ⟩
      (F₁ F) (f • g) fx
        ≡⟨ homomorphism F fx ⟩
      (F₁ F f) ((F₁ F g) fx)
        ≡⟨ refl ⟩
      (F₁ F f) (fx2τx-η fx Y g)
        ∎

    fx2τx-sym-commute : 
      ∀ (fx : (F₀ F) X) {Y Z : Set ℓ} (f : Y → Z) (g : (F₀ (Sets_CYEF X)) Y) → 
        (F₁ F f) (fx2τx-η fx Y g) ≡ fx2τx-η fx Z (F₁ (Sets_CYEF X) f g)
    fx2τx-sym-commute fx {Y} {Z} f g = sym (homomorphism F fx)

    fx2τx : (F₀ F) X → NaturalTransformation (Sets_CYEF X) F
    fx2τx fx = record
      { η = fx2τx-η fx
      ; commute = fx2τx-commute fx
      ; sym-commute = fx2τx-sym-commute fx
      }

    postulate
      sets-nt-eq : {F G : Functor (Sets ℓ) (Sets ℓ)} {α β : NaturalTransformation F G} →
        (∀ Y → η α Y ≡ η β Y) → α ≡ β

    equivalence : NaturalTransformation (Sets_CYEF X) F ⇿ (F₀ F) X
    equivalence = record
      { to = τx2fx
      ; from = fx2τx
      ; to_from = funext (identity F)
      ; from_to = 
          funext (λ τ → 
            sets-nt-eq (λ Y → 
              funext (λ f → sym (commute τ f idf))))
      }
```

## Standard CoYoneda Equivalence

The standard coEndoYoneda equivalence can be generalized to the standard coYoneda equivalence 
involving a functor, `CYF`, to the category of sets, `Sets ℓ`, from any category, `C`. Moreover,
the encoding of the standard coYoneda equivalence is surprisingly similar to the encoding of the
standard coEndoYoneda equivalence equivalence.

The encoding now uses morphism composition, `_∘_`, and morphism identity, `id`.

The encoding involves using field `strict` to bridge the gap between the equivalence relation, `≈`,
of category `C` and propositional equality `≡`.

So, yes, you will, from time to time, be confronted with some "`strict` usage mumbo-jumbo" but,
frankly, in this document, the `strict` impact is very limited.

Please pay attention to the symbols `≡` and `≈`.

We need `Category` now.

```agda
open import Categories.Category.Core using (Category)
```

We also need tranditivity, `trans`, and congruence `cong` now.

```agda
open import Relation.Binary.PropositionalEquality using (trans; cong)
```

We are ready now for `StandardCoYonedaEquivalence`.

```agda
record StandardCoYonedaEquivalence 
  (C : Category (suc ℓ) ℓ ℓ ) : Set (suc ℓ) where

  private
    module C = Category C

  open C 

  open Relation.Binary.PropositionalEquality.≡-Reasoning

  field
    strict : ∀ {X Y} {f g : X ⇒ Y} → f ≈ g → f ≡ g

  CYF : Obj → Functor C (Sets ℓ)
  CYF X = record
    { F₀ = λ Y → X ⇒ Y
    ; F₁ = λ f g → f ∘ g
    ; identity = λ {Y} g → strict identityˡ
    ; homomorphism = λ {Y Z W f h} g → strict assoc
    ; F-resp-≈ = λ {Y} {Z} {f} {h} f≈h g → strict (∘-resp-≈ˡ f≈h)
    }
```

The `equivalence` definition uses a similar `postulate` about natural transformations.

Only the `from_to` proof is more involved, using `strict`.

```agda
  module StandardEquivalence 
    (F : Functor C (Sets ℓ)) 
    (X : Obj) where

    τx2fx : NaturalTransformation (CYF X) F → (F₀ F) X
    τx2fx τx = η τx X id

    fx2τx-η : (F₀ F) X → ∀ Y → (F₀ (CYF X) Y → (F₀ F) Y)
    fx2τx-η fx Y = λ f → (F₁ F) f fx

    fx2τx-commute : ∀ (fx : (F₀ F) X) {Y Z : Obj} (f : Y ⇒ Z) (g : (F₀ (CYF X)) Y) → 
      fx2τx-η fx Z (F₁ (CYF X) f g) ≡ (F₁ F f) (fx2τx-η fx Y g)
    fx2τx-commute fx {Y} {Z} f g = begin
      fx2τx-η fx Z (F₁ (CYF X) f g)
        ≡⟨ refl ⟩
      fx2τx-η fx Z (f ∘ g)
        ≡⟨ refl ⟩
      (F₁ F) (f ∘ g) fx
        ≡⟨ homomorphism F fx ⟩
      (F₁ F f) ((F₁ F g) fx)
        ≡⟨ refl ⟩
      (F₁ F f) (fx2τx-η fx Y g)
        ∎

    fx2τx-sym-commute : ∀ (fx : (F₀ F) X) {Y Z : Obj} (f : Y ⇒ Z) (g : (F₀ (CYF X)) Y) → 
      (F₁ F f) (fx2τx-η fx Y g) ≡ fx2τx-η fx Z (F₁ (CYF X) f g)
    fx2τx-sym-commute fx {Y} {Z} f g = sym (homomorphism F fx)

    fx2τx : (F₀ F) X → NaturalTransformation (CYF X) F
    fx2τx fx = record
      { η = fx2τx-η fx
      ; commute = fx2τx-commute fx
      ; sym-commute = fx2τx-sym-commute fx
      }

    postulate
      to-sets-nt-eq : {F G : Functor C (Sets ℓ)} {α β : NaturalTransformation F G} →
        (∀ Y → η α Y ≡ η β Y) → α ≡ β

    equivalence : NaturalTransformation (CYF X) F ⇿ (F₀ F) X
    equivalence = record
      { to = τx2fx
      ; from = fx2τx
      ; to_from = funext (identity F)
      ; from_to = 
          funext (λ τ →
            to-sets-nt-eq (λ Y →
              funext (λ f → trans (sym (commute τ f id)) (cong (η τ Y) (strict identityʳ)))))
      }
```

## General CoEndoYoneda Equivalence

In the previous sections we first considered endofunctors `F : Functor (Sets ℓ) (Sets ℓ)`, and next
generalized to functors `F : Functor C (Sets ℓ)` for any category `C`. It turned out that this
generalalization was surprisingly straightforward.

In this section we are going to generalize to endofunctors `F : Functor C C` by requiring category
`C` to be a functional category coming with a functor `FF : Functor (Sets ℓ) C` called functional
functor. This functor can then be composed with functor `CYF : Obj → Functor C (Sets ℓ)` to obtain
an endofunctor `CYEF : Obj → Functor C C`.

Think of `FF` as declaring functions as pure morphisms, similar to the `arr` member of
`class Arrow` in Haskell.

Since `Sets ℓ` is no more involved, we are going to work in a pointfree way with morphisms that are
"global like" elements instead of in a pointful way with elements.

First we make the terminal `⊤` object of `Sets ℓ` and it's unique element `tt` available.

```agda
open import Data.Unit using (⊤; tt)
```

Next we make level lifting available.

```agda
open import Level using (Lift; lift)
```

Next we make functor composition and functor identity available, `renaming` the latter.

```agda
open import Categories.Functor using (_∘F_) renaming (id to idF)
```

The basic functional category, `record BasicFunctionalCategory`, is parameterized by a category
`C : Category (suc ℓ) ℓ ℓ` and a functional functor `FF : Functor (Sets ℓ) C`. 

We define `T = Lift ℓ ⊤`, a lifted version of `⊤` and `t = lift tt`, a lifted version of `tt`.

Using `T` we define some convenient abbreviations

- `FFT` for `FF` applied at object level to `T`
- `GEFF` for some "global like" endofunctor involving `CYEF` and `FF`

We declare a monadic unit like natural transformation `nu` and define an abbreviation for its
morphisms as `ηu`.

`nu` comes with with a law `nu-eq-T` relating it with `FF`. 

```agda
record BasicFunctionalCategory
    (C : Category (suc ℓ) ℓ ℓ) 
    (FF : Functor (Sets ℓ) C) : Set (suc ℓ) where
  private
    module C = Category C
    module FF = Functor FF

  open C
  
  field
    strict : ∀ {X Y} {f g : X ⇒ Y} → f ≈ g → f ≡ g

  T : Set ℓ
  T = Lift ℓ ⊤

  t : T
  t = lift tt

  CYF : Obj → Functor C (Sets ℓ)
  CYF X = record
    { F₀ = λ Y → X ⇒ Y
    ; F₁ = λ f g → f ∘ g
    ; identity = λ {Y} g → strict identityˡ
    ; homomorphism = λ {Y Z W f h} g → strict assoc
    ; F-resp-≈ = λ {Y} {Z} {f} {h} f≈h g → strict (∘-resp-≈ˡ f≈h)
    }

  CYEF : Obj → Functor C C
  CYEF X = FF ∘F (CYF X)

  FFT : Obj
  FFT = FF.F₀ T

  GEFF : Functor C C
  GEFF = CYEF FFT 

  field
    nu : NaturalTransformation idF GEFF
    nu-eq-T : η nu (FF.F₀ T) ≡ FF.F₁ (λ _ → FF.F₁ (λ _ → t))

  ηu : ∀ X → X ⇒ F₀ GEFF X
  ηu = η nu
```

The functional category `FunctionalCategory` declares a basic functional category
`bfc : BasicFunctionalCategory C FF` and makes it available for further usage.

Using `T` we define some convenient abbreviation
- `GFF` for some "global like" functor involving `CYF` and `FF`

`nu` now comes with with a law `nu-eq` relating it with `FF`. `nu-eq-T` is a special case of
`nu-eq` as illustrated with `nu-eq-T'`, a `private` definition that is never used. 

We declare a monadic multiplication like natural transformation `mu` and define an abbreviation for its
morphisms as `ηm`.

`mu` comes with with a monadic left identity law `monad-idˡ` (the monadic right identity law
`monad-idʳ` is not needed and is commented out). 


```agda
record FunctionalCategory 
    (C : Category (suc ℓ) ℓ ℓ) 
    (FF : Functor (Sets ℓ) C) : Set (suc ℓ) where
  private
    module C = Category C
    module FF = Functor FF

  open C
  
  field
    bfc : BasicFunctionalCategory C FF

  open BasicFunctionalCategory bfc public

  GFF : Functor C (Sets ℓ)
  GFF = CYF FFT

  field
    nu-eq : ∀ {W : Set ℓ} → η nu (FF.F₀ W) ≈ FF.F₁ (λ w → FF.F₁ (λ _ → w))

    mu : NaturalTransformation (GEFF ∘F GEFF) GEFF  

    monad-idˡ : ∀ {X} → η mu X ∘ η nu (F₀ GEFF X) ≈ C.id
    -- monad-idʳ : ∀ {X} → η mu X ∘ F₁ GEFF (η nu X) ≈ C.id    

  private nu-eq-T' : η nu (FF.F₀ T) ≡ FF.F₁ (λ (t : T) → FF.F₁ (λ _ → t))
  nu-eq-T' = strict (nu-eq {W = T})

  ηm : ∀ X → F₀ (GEFF ∘F GEFF) X ⇒ F₀ GEFF X
  ηm = η mu
```

The coEndoYoneda equivalence is a pointfree version of the standard coEndoYoneda equivalence. It
replaces elements with morphisms that are "global like" elements and it replaces function
application with morphism composition. 

We define some convenient abbreviations

- `G` for `GEFF`
- `GG` for `GFF ∘F GEFF`

The most important definitions are

- `τx2ggfx τx = η τx X ∘ FF.F₁ (λ _ → C.id)`
  cfr. `τx2fx τx = η τx X C.id` 
- `ggfx2τx-η ggfx Y = ηm (F₀ F Y) ∘ FF.F₁ (λ f → F₁ (G ∘F F) f ∘ ggfx)`
  cfr.`fx2τx-η fx Y = λ f → (F₁ F) f fx`

The coEndoYoneda equivalence and standard coEndoYoneda equivalence are similar
"getting the types right puzzles".

This time `ηm (F₀ F Y)` is used as a "getting the types right puzzle" correction.

The `equivalence` definition uses a similar `postulate` about natural transformations.

This time both the `to_from` proof and the `from_to` proof are more involved, using `strict`.

Note that, this time, `HomReasoning` is used.

```agda
record CoEndoYonedaEquivalence 
  (C : Category (suc ℓ) ℓ ℓ )
  (FF : Functor (Sets ℓ) C) : Set (suc ℓ) where

  private
    module C = Category C
    module FF = Functor FF

  open C

  field
    fc : FunctionalCategory C FF

  open FunctionalCategory fc

  module Equivalence {F : Functor C C} {X : Obj} where
    open HomReasoning
    open Equiv renaming (refl to h-refl; sym to h-sym)

    G : Functor C C
    G = GEFF

    GG : Functor C (Sets ℓ)
    GG = GFF ∘F GEFF

    τx2ggfx : NaturalTransformation (CYEF X) (G ∘F F) → F₀ (GG ∘F F) X
    τx2ggfx τx = η τx X ∘ FF.F₁ (λ _ → C.id)

    ggfx2τx-η : F₀ (GG ∘F F) X → ∀ Y → (F₀ (CYEF X) Y) ⇒ (F₀ (G ∘F F) Y)
    ggfx2τx-η ggfx Y = ηm ((F₀ F) Y) ∘ FF.F₁ (λ f → F₁ (G ∘F F) f ∘ ggfx)

    ggfx2τx-commute : 
      ∀ (ggfx : F₀ (GG ∘F F) X) {Y Z : Obj} (f : Y ⇒ Z) → 
        (ggfx2τx-η ggfx Z ∘ F₁ (CYEF X) f) ≈ (F₁ (G ∘F F) f ∘ ggfx2τx-η ggfx Y)
    ggfx2τx-commute ggfx {Y} {Z} f = begin
      ggfx2τx-η ggfx Z ∘ F₁ (CYEF X) f
        ≈⟨ h-refl ⟩
      (ηm (F₀ F Z) ∘ FF.F₁ (λ g → F₁ (G ∘F F) g ∘ ggfx)) ∘ FF.F₁ (λ g → f ∘ g)
        ≈⟨ assoc ⟩
      ηm (F₀ F Z) ∘ (FF.F₁ (λ g → F₁ (G ∘F F) g ∘ ggfx) ∘ FF.F₁ (λ g → f ∘ g))
        ≈⟨ ∘-resp-≈ʳ (h-sym (homomorphism FF)) ⟩
      ηm (F₀ F Z) ∘ FF.F₁ (λ g → F₁ (G ∘F F) (f ∘ g) ∘ ggfx)
        ≈⟨ ∘-resp-≈ʳ (F-resp-≈ FF (λ g → strict (∘-resp-≈ˡ (homomorphism (G ∘F F))))) ⟩
      ηm (F₀ F Z) ∘ FF.F₁ (λ g → (F₁ (G ∘F F) f ∘ F₁ (G ∘F F) g) ∘ ggfx)
        ≈⟨ ∘-resp-≈ʳ (F-resp-≈ FF (λ g → strict assoc)) ⟩
      ηm (F₀ F Z) ∘ FF.F₁ (λ g → F₁ (G ∘F F) f ∘ (F₁ (G ∘F F) g ∘ ggfx))
        ≈⟨ ∘-resp-≈ʳ (homomorphism FF {f = λ g → F₁ (G ∘F F) g ∘ ggfx} {g = λ x → F₁ (G ∘F F) f ∘ x}) ⟩
      ηm (F₀ F Z) ∘ (FF.F₁ (λ x → F₁ (G ∘F F) f ∘ x) ∘ FF.F₁ (λ g → F₁ (G ∘F F) g ∘ ggfx))
        ≈⟨ h-sym assoc ⟩
      (ηm (F₀ F Z) ∘ FF.F₁ (λ x → F₁ (G ∘F F) f ∘ x)) ∘ FF.F₁ (λ g → F₁ (G ∘F F) g ∘ ggfx)
        ≈⟨ ∘-resp-≈ˡ (commute mu {X = F₀ F Y} {Y = F₀ F Z} (F₁ F f)) ⟩
      (F₁ (G ∘F F) f ∘ ηm (F₀ F Y)) ∘ FF.F₁ (λ g → F₁ (G ∘F F) g ∘ ggfx)
        ≈⟨ assoc ⟩
      F₁ (G ∘F F) f ∘ (ηm (F₀ F Y) ∘ FF.F₁ (λ g → F₁ (G ∘F F) g ∘ ggfx))
        ≈⟨ h-refl ⟩
      F₁ (G ∘F F) f ∘ ggfx2τx-η ggfx Y
        ∎

    ggfx2τx-sym-commute : ∀ (ggfx : FF.F₀ T ⇒ (F₀ (G ∘F F) X)) {Y Z : C.Obj} (f : C._⇒_ Y Z) → 
      ((F₁ (G ∘F F) f) ∘ (ggfx2τx-η ggfx Y)) ≈ ((ggfx2τx-η ggfx Z) ∘ (F₁ (CYEF X) f))
    ggfx2τx-sym-commute ggfx f = h-sym (ggfx2τx-commute ggfx f)

    ggfx2τx : F₀ (GG ∘F F) X → NaturalTransformation (CYEF X) (G ∘F F)
    ggfx2τx ggfx = record
      { η = ggfx2τx-η ggfx
      ; commute = ggfx2τx-commute ggfx 
      ; sym-commute = ggfx2τx-sym-commute ggfx
      }

    postulate
      nt-eq : {F G : Functor C C} {α β : NaturalTransformation F G} →
        (∀ Y → η α Y ≡ η β Y) → α ≡ β

    equivalence : NaturalTransformation (CYEF X) (G ∘F F) ⇿ F₀ (GG ∘F F) X
    equivalence = record
      { to = τx2ggfx
      ; from = ggfx2τx
      ; to_from = 
          funext (λ ggfx → strict (begin
            τx2ggfx (ggfx2τx ggfx)
              ≈⟨ h-refl ⟩
            (ηm (F₀ F X) ∘ FF.F₁ (λ f → F₁ (G ∘F F) f ∘ ggfx)) ∘ FF.F₁ (λ _ → C.id)
              ≈⟨ assoc ⟩
            ηm (F₀ F X) ∘ (FF.F₁ (λ f → F₁ (G ∘F F) f ∘ ggfx) ∘ FF.F₁ (λ _ → C.id))
              ≈⟨ ∘-resp-≈ʳ (h-sym (homomorphism FF)) ⟩
            ηm (F₀ F X) ∘ FF.F₁ (λ x → F₁ (G ∘F F) C.id ∘ ggfx)
              ≈⟨ ∘-resp-≈ʳ (F-resp-≈ FF (λ x → strict (∘-resp-≈ˡ (identity (G ∘F F))))) ⟩
            ηm (F₀ F X) ∘ FF.F₁ (λ x → C.id ∘ ggfx)
              ≈⟨ ∘-resp-≈ʳ (F-resp-≈ FF (λ x → strict identityˡ)) ⟩
            ηm (F₀ F X) ∘ FF.F₁ (λ _ → ggfx)
              ≈⟨ ∘-resp-≈ʳ (F-resp-≈ FF (λ t → strict (h-sym identityʳ))) ⟩
            ηm (F₀ F X) ∘ FF.F₁ (λ t → ggfx ∘ C.id)
              ≈⟨ ∘-resp-≈ʳ (F-resp-≈ FF (λ t → strict (∘-resp-≈ʳ (h-sym (identity FF))))) ⟩
            ηm (F₀ F X) ∘ FF.F₁ (λ t → ggfx ∘ FF.F₁ (λ _ → t))
              ≈⟨ ∘-resp-≈ʳ 
                  (homomorphism FF {f = λ t → FF.F₁ (λ _ → t)} {g = λ k → ggfx ∘ k}) ⟩
            ηm (F₀ F X) ∘ (F₁ GEFF ggfx ∘ FF.F₁ (λ t → FF.F₁ (λ _ → t)))
              ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ (h-sym nu-eq)) ⟩
            ηm (F₀ F X) ∘ (F₁ GEFF ggfx ∘ ηu FFT)
              ≈⟨ ∘-resp-≈ʳ (h-sym (commute nu ggfx)) ⟩
            ηm (F₀ F X) ∘ (ηu (F₀ (G ∘F F) X) ∘ ggfx)
              ≈⟨ h-sym assoc ⟩
            (ηm (F₀ F X) ∘ ηu (F₀ GEFF (F₀ F X))) ∘ ggfx
              ≈⟨ ∘-resp-≈ˡ monad-idˡ ⟩
            C.id ∘ ggfx
              ≈⟨ identityˡ ⟩
            ggfx
            ∎
      ))
      ; from_to = 
          funext (λ τ →
            nt-eq (λ Y → strict (begin
              ggfx2τx-η (τx2ggfx τ) Y
                ≈⟨ h-refl ⟩
              ηm (F₀ F Y) ∘ FF.F₁ (λ f → F₁ (G ∘F F) f ∘ (η τ X ∘ FF.F₁ (λ _ → C.id)))
                ≈⟨ ∘-resp-≈ʳ (F-resp-≈ FF (λ f → strict (h-sym assoc))) ⟩
              ηm (F₀ F Y) ∘ FF.F₁ (λ f → (F₁ (G ∘F F) f ∘ η τ X) ∘ FF.F₁ (λ _ → C.id))
                ≈⟨ ∘-resp-≈ʳ (F-resp-≈ FF (λ f → strict (∘-resp-≈ˡ (h-sym (commute τ f))))) ⟩
              ηm (F₀ F Y) ∘ FF.F₁ (λ f → (η τ Y ∘ F₁ (CYEF X) f) ∘ FF.F₁ (λ _ → C.id))
                ≈⟨ ∘-resp-≈ʳ (F-resp-≈ FF (λ f → strict assoc)) ⟩
              ηm (F₀ F Y) ∘ FF.F₁ (λ f → η τ Y ∘ (F₁ (CYEF X) f ∘ FF.F₁ (λ _ → C.id)))
                ≈⟨ ∘-resp-≈ʳ 
                    (F-resp-≈ FF (λ f → strict (∘-resp-≈ʳ (h-sym (homomorphism FF))))) ⟩
              ηm (F₀ F Y) ∘ FF.F₁ (λ f → η τ Y ∘ FF.F₁ (λ x → f ∘ C.id))
                ≈⟨ ∘-resp-≈ʳ 
                    (F-resp-≈ FF (λ f → strict (∘-resp-≈ʳ
                      (F-resp-≈ FF (λ x → strict identityʳ))))) ⟩
              ηm (F₀ F Y) ∘ FF.F₁ (λ f → η τ Y ∘ FF.F₁ (λ _ → f))
                ≈⟨ ∘-resp-≈ʳ 
                    (homomorphism FF {f = λ f → FF.F₁ (λ _ → f)} {g = λ k → η τ Y ∘ k}) ⟩
              ηm (F₀ F Y) ∘ (F₁ GEFF (η τ Y) ∘ FF.F₁ (λ f → FF.F₁ (λ _ → f)))
                ≈⟨ h-sym assoc ⟩
              (ηm (F₀ F Y) ∘ F₁ GEFF (η τ Y)) ∘ FF.F₁ (λ f → FF.F₁ (λ _ → f))
                ≈⟨ ∘-resp-≈ʳ (h-sym nu-eq) ⟩
              (ηm (F₀ F Y) ∘ F₁ GEFF (η τ Y)) ∘ ηu (FF.F₀ (X ⇒ Y))
                ≈⟨ assoc ⟩
              ηm (F₀ F Y) ∘ (F₁ GEFF (η τ Y) ∘ ηu (FF.F₀ (X ⇒ Y)))
                ≈⟨ ∘-resp-≈ʳ (h-sym (commute nu (η τ Y))) ⟩
              ηm (F₀ F Y) ∘ (ηu (F₀ GEFF (F₀ F Y)) ∘ η τ Y)
                ≈⟨ h-sym assoc ⟩
              (ηm (F₀ F Y) ∘ ηu (F₀ GEFF (F₀ F Y))) ∘ η τ Y
                ≈⟨ ∘-resp-≈ˡ monad-idˡ ⟩
              C.id ∘ η τ Y
                ≈⟨ identityˡ ⟩
              η τ Y
              ∎
        )))
      }   
```

## The bad news and the good news (every disadvantage has an advantage)

So we have defined requirements for categories to enable to state and prove a pointfree
coEndoYoneda equivalence.

But, apart from, trivially, `Sets ℓ`, sets with pure functions satisfying those requirements, are
there any other interesting categories satisfying those requirements? 

It turns out is hard to find any.

In fact, in the setting of morphisms being monad-valued functions, a.k.a. Kleisli functions, it is
impossible to find any categories because the requirements of `BasicFunctionalCategory` imply
pureness.

## The purity theorem

We need `Monad`, `Kleisli` and also some `TripleNotation`

```agda
open import Categories.Monad using (Monad)

open import Categories.Category.Construction.Kleisli 
  using (Kleisli; module TripleNotation)
```

So let us start

```agda
module PurityTheorem (M : Monad (Sets ℓ)) where
```

We need `BasicFunctionalCategory` and we are back to equational reasoning.

```agda
  open BasicFunctionalCategory

  open Relation.Binary.PropositionalEquality.≡-Reasoning

  open TripleNotation M
```

Again we define some convenient abbreviations

```agda
  SetsObj : Set (suc ℓ)
  SetsObj = (Sets ℓ).Category.Obj

  MF₀ : SetsObj → SetsObj
  MF₀ X = F₀ (Monad.F M) X

  mPure : {X : SetsObj} → X → MF₀ X
  mPure {X} = η (Monad.η M) X

  mMap : {X Y : SetsObj} → (X → Y) → (MF₀ X → MF₀ Y)
  mMap = F₁ (Monad.F M)

  mApply : {X Y : SetsObj} → (X → MF₀ Y) → (MF₀ X → MF₀ Y)
  mApply f x = (f *) x
```

First we define Kleisli functor, `KF`, mapping functions to pure Kleisli functions.

Next we use `KF` to define the `Kleisli M` `BasicFunctionalCategory` instance.

Next we define `mPure-mMap-eq`, a specific instance of the Kleisli `Hom` reasoning law `sym *⇒F₁`

```agda
  KF : Functor (Sets ℓ) (Kleisli M)
  KF = record
    { F₀ = λ X → X
    ; F₁ = (mPure •_)
    ; identity = λ x → refl
    ; homomorphism = λ {X Y Z f g} x → sym (*-identityʳ {k = mPure • g} (f x))
    ; F-resp-≈ = λ f≈g x → cong mPure (f≈g x)
    }

  KleisliBasicFunctionalCategory : Set (suc ℓ)
  KleisliBasicFunctionalCategory = BasicFunctionalCategory (Kleisli M) KF

  mPure-mMap-eq : ∀ {X} (mx : MF₀ X) → mMap mPure mx ≡ mApply (mPure • mPure) mx
  mPure-mMap-eq {X} mx = sym (*⇒F₁ {X = X} {Y = MF₀ X} {f = mPure} mx)
```

### Advanced Equality Mechanics

To prove that the records in our purity theorems are equal, we will need some advanced equality
tools. Specifically, we need heterogeneous equality `_≅_` (to equate things living in different
types) and implicit function extensionality `funextI` (to prove equality of functions with implicit
arguments).

```agda
  open import Relation.Binary.HeterogeneousEquality using (_≅_)
  open import Axiom.Extensionality.Propositional using (implicit-extensionality)

  funextI : ∀ {a b} → Axiom.Extensionality.Propositional.ExtensionalityImplicit a b
  funextI = implicit-extensionality funext
```

In the setting of Kleisli functions, the concept of an idempotent monad
(see [nLab](https://ncatlab.org/nlab/show/idempotent+monad)) will play an essential role.

Doing something impure twice being the same as doing it once sounds like doing nothing impure at
all.

```agda
  record Idempotent : Set (suc ℓ) where
    field
      idempotent : {X : SetsObj} (mx : MF₀ X) → mMap mPure mx ≡ mPure mx

  open Idempotent
```

We are ready now for the purity theorem : `KleisliBasicFunctionalCategory` and `Idempotent` are
equivalent.

> [!WARNING]
> **Hom-reasoning (`≈`) vs Equational Reasoning (`≡`)**
> 
As you read the following proofs, pay close attention to the difference between `≈` and `≡`. 

In a Kleisli category, `f ≈ g` represents pointwise equality (`∀ x → f x ≡ g x`). 

When we use `≈`, we are doing standard hom-reasoning within the category.

However, to prove that two records are equal, their fields must be propositionally equal (`≡`).

Proving that `f ≡ g` requires equational reasoning and often invokes function extensionality
(`funext`).

Copy-pasting proofs from hom-reasoning into equational reasoning blocks will cause frustrating type
errors because the symbols look almost identical but have entirely different semantic requirements!

Anyway, note that we are, essentially, back to equational reasoning.

Note that the code is work in progress and some of the `trans` usages are likely to be replaced by
equational reasoning `begin ... ∎` code.
 
`BasicFunctionalCategory` is a dependent `record`. The type of the `nu` field  depends on the
`strict` field, making standard propositional equality `≡` impossible to state directly.

We postulate the structural assembly of the  dependent record using heterogeneous equality `≅` to
bypass the boilerplate.

The `strict` field is uniquely determined by uniqueness of identity proofs `uip` and function
extensionality, so any two instances are propositionally equal.

The `nu` field is uniquely determined by the categorical structures involved.
We postulate this heterogeneous equality as the structural uniqueness principle.

```agda
  postulate
    bfc-eq : 
      (a b : KleisliBasicFunctionalCategory)
        → (λ {X Y f g} → BasicFunctionalCategory.strict a {X} {Y} {f} {g}) ≡ 
            (λ {X Y f g} → BasicFunctionalCategory.strict b {X} {Y} {f} {g})
        → BasicFunctionalCategory.nu a ≅ BasicFunctionalCategory.nu b
          → a ≡ b

  uip : ∀ {a} {A : Set a} {x y : A} (p q : x ≡ y) → p ≡ q
  uip refl refl = refl

  postulate
    strict-eq : 
      (a b : KleisliBasicFunctionalCategory) → 
        (λ {X Y f g} → BasicFunctionalCategory.strict a {X} {Y} {f} {g}) ≡ 
          (λ {X Y f g} → BasicFunctionalCategory.strict b {X} {Y} {f} {g})

    nu-heq : 
      (a b : KleisliBasicFunctionalCategory) → 
        BasicFunctionalCategory.nu a ≅ BasicFunctionalCategory.nu b

  kleisli-basic-functional-category-eq-prop : ∀ {a b : KleisliBasicFunctionalCategory} → a ≡ b
  kleisli-basic-functional-category-eq-prop {a} {b} = bfc-eq a b (strict-eq a b) (nu-heq a b)

  mkIdempotent : (p : {X : SetsObj} (mx : MF₀ X) → mMap mPure mx ≡ mPure mx) → Idempotent
  mkIdempotent p = record { idempotent = p }

  idempotent-eq : 
    (i1 i2 : Idempotent) → 
      (∀ {X} mx → Idempotent.idempotent i1 {X} mx ≡ Idempotent.idempotent i2 {X} mx) → i1 ≡ i2
  idempotent-eq (record { idempotent = idem1 }) (record { idempotent = idem2 }) p = 
    cong mkIdempotent (funextI (λ {X} → funext (λ mx → p {X} mx)))

  idempotent-eq-prop : ∀ {a b : Idempotent} → a ≡ b
  idempotent-eq-prop {a} {b} = idempotent-eq a b (λ {X} mx → uip _ _)

  idempotent-equiv-kleisli-basic-functional-category : 
    KleisliBasicFunctionalCategory ⇿ Idempotent
  idempotent-equiv-kleisli-basic-functional-category = record
    { to = λ kbfc → record 
        { idempotent = λ {X} mx → 
            let
              T = Lift ℓ ⊤
              t = lift tt
              MX = MF₀ X
              GMX = T → MX
              gmx = λ (_ : T) → mx
              MGMX = MF₀ GMX
              _∘K_ = Category._∘_ (Kleisli M)
              
              sigma-eval-lemma : 
                ∀ {Z : SetsObj} (mz : MF₀ Z) →
                  mApply {Z} {T → MF₀ Z} (η (nu kbfc) Z) mz ≡ mPure (λ _ → mz)
              sigma-eval-lemma {Z} mz =
                let
                  MZ = MF₀ Z
                  GMZ = T → MZ     
                  gmz = λ (_ : T) → mz

                  nat-at-t : 
                    (F₁ (GEFF kbfc) gmz ∘K η (nu kbfc) T) t ≡ 
                      (η (nu kbfc) Z ∘K gmz) t
                  nat-at-t = sym (commute (nu kbfc) gmz t)

                  left-eq : 
                     (F₁ (GEFF kbfc) gmz ∘K η (nu kbfc) T) t ≡ mPure gmz
                  left-eq = 
                    begin
                      mApply (F₁ (GEFF kbfc) gmz) (η (nu kbfc) T t)
                        ≡⟨ cong (λ k → 
                            mApply (F₁ (GEFF kbfc) gmz) k) (cong (λ k → k t) (nu-eq-T kbfc)) ⟩
                      mApply (F₁ (GEFF kbfc) gmz) (mPure (λ _ → mPure t))
                        ≡⟨ *-identityʳ {k = F₁ (GEFF kbfc) gmz} (λ _ → mPure t) ⟩
                      F₁ (GEFF kbfc) gmz (λ _ → mPure t)
                        ≡⟨ refl ⟩
                      mPure (λ _ → mApply gmz (mPure t))
                        ≡⟨ cong (λ k → mPure (λ _ → k)) (*-identityʳ {k = gmz} t) ⟩
                      mPure (λ _ → gmz t)
                        ≡⟨ refl ⟩
                      mPure gmz
                    ∎
                  right-eq : 
                     (η (nu kbfc) Z ∘K gmz) t ≡ mApply (η (nu kbfc) Z) mz
                  right-eq = refl

                in trans (sym right-eq) (trans (sym nat-at-t) left-eq)
        
              eval = λ (mgmx : MGMX) → mApply (λ gmx → mPure (gmx t)) mgmx
              
              step1 : eval (mApply (η (nu kbfc) X) mx) ≡ eval (mPure gmx)
              step1 = cong eval (sigma-eval-lemma mx)
              
              step2 : eval (mPure gmx) ≡ mPure mx
              step2 = *-identityʳ {k = λ g → mPure (g t)} gmx
              
              step3 : eval (mApply (η (nu kbfc) X) mx) ≡ mApply (mPure • mPure) mx
              step3 = begin
                mApply (λ g → mPure (g t)) (mApply (η (nu kbfc) X) mx)
                  ≡⟨ sym 
                      (*-assoc {k = η (nu kbfc) X} {l = λ g → mPure (g t)} mx) ⟩
                mApply (λ x → mApply (λ g → mPure (g t)) (η (nu kbfc) X x)) mx
                  ≡⟨ cong (λ k → mApply k mx) (funext (λ x → 
                       let
                         inner = sigma-eval-lemma (mPure x)
                         inner-eval :
                          eval (mApply (η (nu kbfc) X) (mPure x)) ≡ 
                            eval (mPure (λ _ → mPure x))
                         inner-eval = cong eval inner
                         inner-eval2 : eval (mPure (λ _ → mPure x)) ≡ mPure (mPure x)
                         inner-eval2 = *-identityʳ {k = λ g → mPure (g t)} (λ _ → mPure x)
                         inner-eval3 :
                           eval (mApply (η (nu kbfc) X) (mPure x)) ≡ eval (η (nu kbfc) X x)
                         inner-eval3 = cong eval (*-identityʳ {k = η (nu kbfc) X} x)
                       in trans (sym inner-eval3) (trans inner-eval inner-eval2)
                     )) ⟩
                mApply (λ x → mPure (mPure x)) mx
                  ∎
            in trans (mPure-mMap-eq mx) (trans (sym step3) (trans step1 step2))
        }
    ; from = λ i → 
        let
          T = Lift ℓ ⊤

          nu-mApply-lemma : 
            ∀ {Z} (mz : MF₀ Z) → mApply (λ z → mPure {T → MF₀ Z} (λ _ → mPure z)) mz ≡ 
              mPure {T → MF₀ Z} (λ _ → mz)
          nu-mApply-lemma {Z} mz = 
            let 
              MZ = MF₀ Z
              GMZ = T → MZ            
              gmz = λ (_ : T) → mz
              MGMZ = MF₀ GMZ
              mz2mgmz = λ (mz : MZ) → mPure {GMZ} (λ _ → mz)
            in begin
              mApply (λ z → mPure (λ _ → mPure z)) mz
                ≡⟨ sym (cong (λ k → mApply k mz) (funext (λ (z : Z) → 
                      *-identityʳ {k = mz2mgmz} (mPure z)))) ⟩
              mApply (λ z → mApply mz2mgmz (mPure {MZ} (mPure z))) mz
                ≡⟨ *-assoc {k = λ z → mPure (mPure z)} {l = mz2mgmz} mz ⟩
              mApply mz2mgmz (mApply (λ z → mPure (mPure z)) mz)
                ≡⟨ cong 
                    (λ mz → mApply mz2mgmz mz) 
                      (trans (sym (mPure-mMap-eq mz)) (idempotent i mz)) ⟩
              mApply mz2mgmz (mPure mz)
                ≡⟨ *-identityʳ {k = mz2mgmz} mz ⟩
              mPure gmz
                ∎
          
          comm : ∀ {X} {Y} (gmx2mx : X → MF₀ Y) (x : X) → 
            mApply (λ z → mPure {T → MF₀ Y} (λ _ → mPure {Y} z)) (gmx2mx x) ≡ 
              mApply (mPure • (λ g t → mApply gmx2mx (g t))) 
                (mPure {T → MF₀ X} (λ _ → mPure {X} x))
          comm {X} {Y} gmx2mx x = 
                 let 
                   comm-lhs : 
                    mApply (mPure • (λ g u → mApply gmx2mx (g u))) (mPure (λ _ → mPure x)) ≡
                      mPure (λ _ → gmx2mx x)
                   comm-lhs = begin
                     mApply (mPure • (λ g u → mApply gmx2mx (g u))) (mPure (λ _ → mPure x))
                       ≡⟨ *-identityʳ {k = mPure • (λ g u → mApply gmx2mx (g u))} (λ _ → mPure x) ⟩
                     mPure (λ u → mApply gmx2mx (mPure x))
                       ≡⟨ cong (λ k → mPure (λ _ → k)) (*-identityʳ {k = gmx2mx} x) ⟩
                     mPure (λ _ → gmx2mx x)
                       ∎
                 in sym (trans comm-lhs (sym (nu-mApply-lemma (gmx2mx x))))
        in
        record { strict = λ f≈g → funext f≈g
               ; nu = record 
                  { η = λ X x → mPure {T → MF₀ X} (λ _ → mPure {X} x)
                  ; commute = comm
                  ; sym-commute = λ f x → sym (comm f x)
                  } 
               ; nu-eq-T = refl
              }
    ; to_from = funext (λ i → idempotent-eq-prop)
    ; from_to = funext (λ kbfc → kleisli-basic-functional-category-eq-prop)
    }
```

We now define `EnforcingPurity` which is equivalent with `Idempotent`.

```agda
  record EnforcingPurity : Set (suc ℓ) where
    field
      enforcingPurity : {X : SetsObj} (mx : MF₀ X) → mApply (mPure • mPure) mx ≡ mPure mx

  open EnforcingPurity

  mkEnforcingPurity : 
    (p : {X : SetsObj} (mx : MF₀ X) → mApply (mPure • mPure) mx ≡ mPure mx) → EnforcingPurity
  mkEnforcingPurity p = record { enforcingPurity = p }

  enforcing-purity-eq : 
    (e1 e2 : EnforcingPurity) → 
      (∀ {X} mx → EnforcingPurity.enforcingPurity e1 {X} mx ≡ 
        EnforcingPurity.enforcingPurity e2 {X} mx) → e1 ≡ e2
  enforcing-purity-eq 
    (record { enforcingPurity = ep1 }) (record { enforcingPurity = ep2 }) p = 
      cong mkEnforcingPurity (funextI (λ {X} → funext (λ mx → p {X} mx)))

  enforcing-purity-eq-prop : ∀ {a b : EnforcingPurity} → a ≡ b
  enforcing-purity-eq-prop {a} {b} = enforcing-purity-eq a b (λ {X} mx → uip _ _)

  idempotent-equiv-enforcing-purity : Idempotent ⇿ EnforcingPurity 
  idempotent-equiv-enforcing-purity = record 
    {
        to = λ i → record
          { enforcingPurity = λ mx → 
              begin
                mApply (mPure • mPure) mx
                  ≡⟨ sym (mPure-mMap-eq mx) ⟩
                mMap mPure mx
                  ≡⟨ idempotent i mx ⟩
                mPure mx
              ∎
          }

      ; from = λ ep → record
            { idempotent = λ mx →
                begin
                  mMap mPure mx
                    ≡⟨ mPure-mMap-eq mx ⟩
                  mApply (mPure • mPure) mx
                    ≡⟨ enforcingPurity ep mx ⟩
                  mPure mx
                ∎
            }
      ; to_from = funext (λ ep → enforcing-purity-eq-prop)
      ; from_to = funext (λ i → idempotent-eq-prop)
    }
```

`Singleton` defines what it means to be a singleton.

```agda
  Singleton : Set ℓ → Set ℓ
  Singleton A = ∀ (x y : A) → x ≡ y
```

The main result is encoded in `enforcing-purity-implies-pure-unit-eq`.

```agda
  enforcing-purity-implies-pure-unit-eq : 
    EnforcingPurity → (mt : MF₀ (Lift ℓ ⊤)) → mt ≡ mPure (lift tt)
  enforcing-purity-implies-pure-unit-eq ep mt =
    let 
      T = Lift ℓ ⊤
      t = lift tt
      MT = MF₀ T
      MMT = MF₀ (MT)      
      μT = mApply {MT} {T} (λ _ → mPure {T} t)
          
      lhs-inner : 
        ∀ x → mApply {MT} {T} (λ _ → mPure t) (mPure (mPure x)) ≡ mPure t
      lhs-inner x = 
        *-identityʳ {x = MT} {y = T} {k = λ _ → mPure t} (mPure {T} x)
      
      ⊤-is-singleton : (a b : T) → a ≡ b
      ⊤-is-singleton t t = refl
      
      lhs-eq : μT (mApply (mPure • mPure) mt) ≡ mt
      lhs-eq = 
        trans (*-sym-assoc {x = T} {y = MT} {z = T}
          {k = λ x → mPure (mPure x)} {l = λ _ → mPure t} mt) 
            (trans (cong (λ f → mApply f mt) (funext lhs-inner)) 
              (trans (cong (λ f → mApply f mt) (funext (λ (x : T) →
                cong mPure (⊤-is-singleton t x)))) (*-identityˡ {T} mt)))
      
    in trans (sym lhs-eq) 
        (trans (cong μT (enforcingPurity ep mt)) 
           (*-identityʳ {x = MT} {y = T} {k = λ _ → mPure t} mt))
```

Purity boils down to `MF₀ (Lift ℓ ⊤)` being a `Singleton` which is the same as `MF₀` being a
trivial computation.
 
```agda 
  TrivialComputation : (Set ℓ → Set ℓ) → Set ℓ
  TrivialComputation MF₀ = Singleton (MF₀ (Lift ℓ ⊤))
```

So now, here is our final result.

```agda
  enforcing-purity-implies-trivial-computation : 
    EnforcingPurity → TrivialComputation MF₀
  enforcing-purity-implies-trivial-computation ep x y =
    trans 
      (enforcing-purity-implies-pure-unit-eq ep x) 
        (sym (enforcing-purity-implies-pure-unit-eq ep y))
```

Here are some concrete examples.

They use `Triple` in order to disambiguate from `Monad`

```agda
open import Level
open import Data.Maybe hiding (_>>=_)
open import Data.List
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty

private
  variable
    u : Level

record Triple {u : Level} (M : Set u → Set u) : Set (suc u) where
  field
    pure : ∀ {X : Set u} → X → M X
    _>>=_ : ∀ {X Y : Set u} → M X → (X → M Y) → M Y

open Triple {{...}}

EnforcingPurityEq : ∀ {u} (M : Set u → Set u) ⦃ _ : Triple M ⦄ → Set (suc u)
EnforcingPurityEq {u} M = ∀ {X : Set u} (mx : M X) → (mx >>= (pure ∘ pure)) ≡ pure mx

instance
  TripleMaybe : ∀ {u} → Triple {u} Maybe
  TripleMaybe = record
    { pure = just
    ; _>>=_ = λ { nothing _ → nothing
                  ; (just x) f → f x
                  }
    }

maybe-not-pure : ∀ {u} → ¬ EnforcingPurityEq {u} Maybe
maybe-not-pure {u} h =
  let T = Lift u ⊤
  in contradiction-from (h (nothing {A = T}))
  where
    T = Lift u ⊤
    contradiction-from : _≡_ {A = Maybe (Maybe T)} nothing (just nothing) → ⊥
    contradiction-from ()

instance
  TripleList : ∀ {u} → Triple {u} List
  TripleList = record
    { pure = λ x → x ∷ []
    ; _>>=_ = λ xs f → concatMap f xs
    }

list-not-pure : ∀ {u} → ¬ EnforcingPurityEq {u} List
list-not-pure {u} h =
  let T = Lift u ⊤
      t = lift tt
  in contradiction-from (h (t ∷ t ∷ []))
  where
    T = Lift u ⊤
    t = lift tt
    contradiction-from : 
      _≡_ {A = List (List T)} ((t ∷ []) ∷ (t ∷ []) ∷ []) ((t ∷ t ∷ []) ∷ []) → ⊥
    contradiction-from ()

MyReader : ∀ {u} → Set u → Set u → Set u
MyReader R X = R → X

instance
  TripleReader : ∀ {u} {R : Set u} → Triple (MyReader R)
  TripleReader = record
    { pure = λ x _ → x
    ; _>>=_ = λ m f r → f (m r) r
    }

SingletonProp : ∀ {u} → Set u → Set u
SingletonProp A = (x y : A) → x ≡ y

reader-purity-implies : ∀ {u} (R : Set u) → EnforcingPurityEq (MyReader R) → SingletonProp R
reader-purity-implies R h r1 r2 =
  cong (λ f → f r1 r2) (h (λ r → r))

MyWriter : ∀ {u} → Set u → Set u → Set u
MyWriter W X = X × W

module WriterTriple {u : Level} (W : Set u) (e : W) (_∙_ : W → W → W) where
  
  instance
    TripleWriter : Triple (MyWriter W)
    TripleWriter = record
      { pure = λ x → (x , e)
      ; _>>=_ = λ mx f → let (y , w) = f (proj₁ mx) in (y , proj₂ mx ∙ w)
      }

  writer-purity-implies : EnforcingPurityEq (MyWriter W) → ∀ w → w ≡ e
  writer-purity-implies h w =
    sym (cong proj₂ (cong proj₁ (h (e , w))))

MyState : ∀ {u} → Set u → Set u → Set u
MyState S X = S → X × S

instance
  TripleState : ∀ {u} {S : Set u} → Triple (MyState S)
  TripleState = record
    { pure = λ x s → (x , s)
    ; _>>=_ = λ mx f s → let (x , s') = mx s in f x s'
    }

state-purity-implies : ∀ {u} (S : Set u) → EnforcingPurityEq (MyState S) → SingletonProp S
state-purity-implies S h s1 s2 =
  cong (λ f → proj₁ (f s2)) (cong (λ f → proj₁ (f s1)) (h (λ s → (s , s))))

MyCont : ∀ {u} → Set u → Set u → Set u
MyCont R X = (X → R) → R

instance
  TripleCont : ∀ {u} {R : Set u} → Triple (MyCont R)
  TripleCont = record
    { pure = λ x k → k x
    ; _>>=_ = λ mx f k → mx (λ x → f x k)
    }

cont-purity-implies : ∀ {u} (R : Set u) → EnforcingPurityEq (MyCont R) → SingletonProp R
cont-purity-implies R h r1 r2 =
  let m1 : MyCont R R
      m1 = λ _ → r1
  in cong (λ f → f (λ _ → r2)) (h m1)

-- `IO` simulated as `MyErrorState`
MyErrorState : ∀ {u} → Set u → Set u → Set u → Set u
MyErrorState E S X = S → (E × S) ⊎ (X × S)

instance
  TripleMyErrorState : ∀ {u} {E S : Set u} → Triple (MyErrorState E S)
  TripleMyErrorState = record
    { pure = λ x w → inj₂ (x , w)
    ; _>>=_ = λ mx f w → [ inj₁ , (λ { (x , w') → f x w' }) ]′ (mx w)
    }

my-io-not-pure : ∀ {u} {E S : Set u} (e : E) (s : S) → ¬ EnforcingPurityEq (MyErrorState E S)
my-io-not-pure {u} {E} {S} e s h =
  let m = λ s → inj₁ (e , s)
  in contradiction-from (cong (λ f → f s) (h m))
  where
    contradiction-from : ∀ {u} {E S : Set u} {e : E} {s : S} {m} 
      → _≡_ {A = (E × S) ⊎ (MyErrorState E S (Lift u ⊤) × S)} (inj₁ (e , s)) (inj₂ (m , s)) → ⊥
    contradiction-from ()
```

