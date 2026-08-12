import sys

with open("CoEndoYonedaEquivalenceAndPurity.lagda.md", "r") as f:
    content = f.read()

# 1. Remove the remaining HeterogeneousEquality import
content = content.replace("  open import Relation.Binary.HeterogeneousEquality using (_≅_)\n", "")

# 2. Replace the markdown documentation
old_markdown = """`BasicFunctionalCategory` is a dependent `record`. The type of the `nu` field  depends on the
`strict` field, making standard propositional equality `≡` impossible to state directly.

We `postulate` the structural assembly of the  dependent record using heterogeneous equality `≅` to
bypass the boilerplate.

The `strict` field is uniquely determined by uniqueness of identity proofs `uip` and function
extensionality, so any two instances are propositionally equal.

The `nu` field is uniquely determined by the categorical structures involved.
We `postulate` this uniqueness using standard propositional equality and `subst`."""

new_markdown = """`BasicFunctionalCategory` is a dependent `record`. The type of the `nu` field depends on the
`strict` field. To prove equality of two such records, we must prove their fields are propositionally equal,
but standard propositional equality `≡` cannot be used directly for `nu` without accounting for the dependency.

Instead of relying on heterogeneous equality (`≅`), we lift the dependent type out into `CYF-helper` and `GEFF-helper`
parameterized by `StrictType`. This allows us to use standard type substitution (`subst`) to explicitly map the `nu` field along the equality of the `strict` fields.

The `strict` field is uniquely determined by uniqueness of identity proofs `uip` and function
extensionality, so any two instances are propositionally equal. We postulate this uniqueness as `strict-kbfc-eq`
for `KleisliBasicFunctionalCategory`. 

The `nu` field is similarly uniquely determined by the categorical structures involved.
We postulate this uniqueness as `nu-eq` using standard propositional equality and `subst`."""

content = content.replace(old_markdown, new_markdown)

# 3. Rename strict-eq and add comment
old_postulate = """  postulate
    strict-eq : 
      (a b : KleisliBasicFunctionalCategory) → 
        (λ {X Y f g} → BasicFunctionalCategory.strict a {X} {Y} {f} {g}) ≡ 
          (λ {X Y f g} → BasicFunctionalCategory.strict b {X} {Y} {f} {g})

    nu-eq : 
      (a b : KleisliBasicFunctionalCategory) 
      → (p : (λ {X Y f g} → BasicFunctionalCategory.strict a {X} {Y} {f} {g}) ≡ (λ {X Y f g} → BasicFunctionalCategory.strict b {X} {Y} {f} {g}))
      → subst (λ (s : StrictType) → NaturalTransformation Categories.Functor.id (GEFF-helper s)) p (BasicFunctionalCategory.nu a) ≡ BasicFunctionalCategory.nu b

  kleisli-basic-functional-category-eq-prop : ∀ {a b : KleisliBasicFunctionalCategory} → a ≡ b
  kleisli-basic-functional-category-eq-prop {a} {b} = bfc-eq a b (strict-eq a b) (nu-eq a b (strict-eq a b))"""

new_postulate = """  -- The `strict` field of a KleisliBasicFunctionalCategory is completely determined 
  -- by function extensionality and uniqueness of identity proofs (uip). 
  -- We postulate this uniqueness here, which serves as the foundational equality 
  -- over which we substitute the rest of the dependent record.
  postulate
    strict-kbfc-eq : 
      (a b : KleisliBasicFunctionalCategory) → 
        (λ {X Y f g} → BasicFunctionalCategory.strict a {X} {Y} {f} {g}) ≡ 
          (λ {X Y f g} → BasicFunctionalCategory.strict b {X} {Y} {f} {g})

    nu-eq : 
      (a b : KleisliBasicFunctionalCategory) 
      → (p : (λ {X Y f g} → BasicFunctionalCategory.strict a {X} {Y} {f} {g}) ≡ (λ {X Y f g} → BasicFunctionalCategory.strict b {X} {Y} {f} {g}))
      → subst (λ (s : StrictType) → NaturalTransformation Categories.Functor.id (GEFF-helper s)) p (BasicFunctionalCategory.nu a) ≡ BasicFunctionalCategory.nu b

  kleisli-basic-functional-category-eq-prop : ∀ {a b : KleisliBasicFunctionalCategory} → a ≡ b
  kleisli-basic-functional-category-eq-prop {a} {b} = bfc-eq a b (strict-kbfc-eq a b) (nu-eq a b (strict-kbfc-eq a b))"""

content = content.replace(old_postulate, new_postulate)

with open("CoEndoYonedaEquivalenceAndPurity.lagda.md", "w") as f:
    f.write(content)

