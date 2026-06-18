/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

Graphon representability (Lovász–Szegedy), Tier-C item 4.

A graph parameter `f` (a real-valued function on finite simple graphs, here canonically
indexed by `SimpleGraph (Fin n)`) is **realizable by a graphon** — i.e. `f F = t(F, W)` for
some graphon `W` over the unit interval — iff `f` is

  * **multiplicative**   `f (F₁ ⊔ F₂) = f F₁ · f F₂` over disjoint unions,
  * **normalized**       `f K₀ = 1` (`K₀` = the empty graph on `0` vertices), and
  * **reflection-positive**  every connection matrix `M(f, k)` is positive semidefinite.

The DISCRETE analogue (finite weighted target graph) is Freedman–Lovász–Schrijver (JAMS 2007),
Thm 2.4; the graphon limit is Lovász–Szegedy. The hard (converse) direction is a true classical
theorem absent from Mathlib; it is OWNED by `reflection-positivity`
(`Graph.FLS.main` + the cut-distance limit). Here it is recorded as the single named axiom
`lovasz_szegedy_representability`, to be discharged there.

The EASY (forward) direction — every `t(·, W)` is multiplicative, normalized and
reflection-positive — is PROVED here:
  * multiplicativity reuses `homDensity_sum`;
  * normalization is `homDensity` of the empty graph on the empty vertex set `= 1`;
  * reflection positivity holds because each connection matrix of hom densities is a **Gram
    matrix**: `t(G₁ ⊙ₖ G₂, W) = ∫_{Ω^k} (partial density of G₁) · (partial density of G₂)`, so the
    associated quadratic form is `∫ (∑ᵢ cᵢ · partialᵢ)² ≥ 0`.

References:
* M. Freedman, L. Lovász, A. Schrijver, *Reflection positivity, rank connectivity, and
  homomorphism of graphs*, JAMS 20 (2007), Thm 2.4.
* L. Lovász, B. Szegedy, *Limits of dense graph sequences*, JCTB 96 (2006).
* L. Lovász, *Large Networks and Graph Limits*, AMS Coll. Publ. 60 (2012), Ch. 5–6.
-/
import Graphons.Core.Multiplicativity

open MeasureTheory

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ## Graph parameters

A **graph parameter** is a real-valued function on finite simple graphs. We let it take a graph on
*any* finite vertex type `V` (`Type` for definiteness); this matches the type of `homDensity` and
spares us from threading vertex-relabelling isomorphisms.  Decidability of adjacency is supplied by
`Classical.dec` where needed, so no `[DecidableRel]` instance has to be carried by `f`. -/

/-- A graph parameter: a real number attached to every finite simple graph. -/
abbrev GraphParam := ⦃V : Type⦄ → [Fintype V] → SimpleGraph V → ℝ

/-! ## Labeled graphs and gluing

A `k`-**labeled graph** with body of size `m` is a `SimpleGraph (Fin k ⊕ Fin m)`; the first `k`
vertices are the (ordered) labels.  Two `k`-labeled graphs are **glued** by identifying their
labels: the result is the graph on `Fin k ⊕ (Fin m₁ ⊕ Fin m₂)` carrying the edges of both
copies (labels shared). -/

/-- Left injection of a `k`-labeled body-`m₁` vertex into the glued vertex set. -/
def glueInl (k m₁ m₂ : ℕ) : Fin k ⊕ Fin m₁ ↪ Fin k ⊕ (Fin m₁ ⊕ Fin m₂) :=
  ⟨Sum.map id Sum.inl, by
    rintro (a | a) (b | b) h <;> simp_all [Sum.map]⟩

/-- Right injection of a `k`-labeled body-`m₂` vertex into the glued vertex set. -/
def glueInr (k m₁ m₂ : ℕ) : Fin k ⊕ Fin m₂ ↪ Fin k ⊕ (Fin m₁ ⊕ Fin m₂) :=
  ⟨Sum.map id Sum.inr, by
    rintro (a | a) (b | b) h <;> simp_all [Sum.map]⟩

/-- **Gluing** two `k`-labeled graphs along their shared labels: the union (`⊔`) of the two
pushforward graphs into `Fin k ⊕ (Fin m₁ ⊕ Fin m₂)`. The labeled vertices `Fin k` are shared. -/
def glue {k m₁ m₂ : ℕ} (G₁ : SimpleGraph (Fin k ⊕ Fin m₁))
    (G₂ : SimpleGraph (Fin k ⊕ Fin m₂)) : SimpleGraph (Fin k ⊕ (Fin m₁ ⊕ Fin m₂)) :=
  G₁.map (glueInl k m₁ m₂) ⊔ G₂.map (glueInr k m₁ m₂)

/-- A `k`-labeled graph is **label-independent** when the `k` labeled vertices carry no edges among
themselves (`G.Adj (.inl a) (.inl b)` never holds).

This is the **standard normalization** for connection matrices (Lovász, *Large Networks and Graph
Limits*, §5.2): one assumes the labeled nodes form an independent set, so that gluing two labeled
graphs takes the *disjoint union of their edge sets* (no edge among labels is identified or
"doubled"). Without it, a simple-graph union `⊔` would merge a label–label edge present in both
factors into one, breaking the Gram factorization `t(G₁ ⊙ G₂) = ⟨t_y(G₁), t_y(G₂)⟩`. The
restriction loses no generality for representability: any partially labeled graph is equivalent
(for the connection-matrix theory) to one with an independent label set. -/
def LabelIndependent {k m : ℕ} (G : SimpleGraph (Fin k ⊕ Fin m)) : Prop :=
  ∀ a b : Fin k, ¬ G.Adj (Sum.inl a) (Sum.inl b)

/-! ## Predicates on graph parameters -/

/-- `f` is **multiplicative**: it sends disjoint unions (`SimpleGraph.sum`, the graph on
`V₁ ⊕ V₂`) to products. -/
def IsMultiplicative (f : GraphParam) : Prop :=
  ∀ {V₁ V₂ : Type} [Fintype V₁] [Fintype V₂] (F₁ : SimpleGraph V₁) (F₂ : SimpleGraph V₂),
    f (F₁.sum F₂) = f F₁ * f F₂

/-- `f` is **normalized**: `f K₀ = 1`, where `K₀` is the empty graph on `0` vertices (here the
edgeless graph `⊥` on the empty type). -/
def IsNormalized (f : GraphParam) : Prop :=
  f (⊥ : SimpleGraph (Fin 0)) = 1

/-- `f` is **reflection-positive**: for every number of labels `k`, every finite family of
label-independent `k`-labeled graphs `G i` (with bodies of arbitrary sizes `m i`) and all real
coefficients `c i`, the quadratic form of the connection matrix
`M(f, k)_{i,j} = f (glue (G i) (G j))` is nonneg: `∑ᵢⱼ cᵢ cⱼ f (glue (G i) (G j)) ≥ 0`.

This is the **streamlined-but-faithful** form of "every connection matrix `M(f, k)` is positive
semidefinite": `M(f, k)` is the (infinite) symmetric matrix indexed by all `k`-labeled graphs with
entries `f (G ⊙ₖ G')`, and an infinite symmetric matrix is PSD exactly when every finite principal
submatrix has nonnegative quadratic form — which is precisely the statement below, ranging over all
finite index families. The graphs are taken **label-independent** (`LabelIndependent`), the standard
connection-matrix normalization (see `LabelIndependent`). -/
def ReflectionPositive (f : GraphParam) : Prop :=
  ∀ (k : ℕ) {ι : Type} [Fintype ι] (m : ι → ℕ)
    (G : ∀ i, SimpleGraph (Fin k ⊕ Fin (m i))) (_hG : ∀ i, LabelIndependent (G i)) (c : ι → ℝ),
    0 ≤ ∑ i, ∑ j, c i * c j * f (glue (G i) (G j))

/-- `f` is **bounded**: it takes values in `[0,1]`. This is FORCED for any hom-density parameter of
a `[0,1]`-valued graphon (`t(F, W) ∈ [0,1]`), and it is an essential hypothesis of the
Lovász–Szegedy graphon theorem: without it, e.g. `f F = 2 ^ (F.edgeFinset.card)` is multiplicative,
normalized and reflection-positive yet `f K₂ = 2 ∉ [0,1]`, so not realizable by a `[0,1]`-graphon. -/
def IsBounded (f : GraphParam) : Prop :=
  ∀ {V : Type} [Fintype V] (F : SimpleGraph V), f F ∈ Set.Icc (0:ℝ) 1

/-- `f` is **realized by a graphon** if it is the hom-density function of some graphon over the
unit interval `([0,1], Lebesgue)`. -/
def RealizedByGraphon (f : GraphParam) : Prop :=
  ∃ W : Graphon ℝ unitMeasure,
    ∀ {V : Type} [Fintype V] (F : SimpleGraph V),
      f F = haveI := Classical.decRel F.Adj; homDensity F W

/-! ## The hard direction: one named axiom

The converse — every multiplicative, normalized, reflection-positive **and `[0,1]`-bounded** graph
parameter is realized by a graphon — is the genuine Lovász–Szegedy graphon theorem (Lovász–Szegedy,
*Limits of dense graph sequences*, JCTB 96 (2006); Lovász, *Large Networks and Graph Limits* (2012),
Thm 5.54 / §5.6, and Thm 14.31). The `[0,1]` value bound (`IsBounded`) is ESSENTIAL: the
finite-weighted **rank-bounded** Freedman–Lovász–Schrijver theorem (JAMS 2007, Thm 2.4) allows
*unbounded* weights with rank `≤ q^k` and is a DISTINCT statement; the graphon theorem here is the
`[0,1]`-bounded one. It is a true classical theorem, absent from Mathlib. It is owned and to be
discharged in `reflection-positivity` via that repo's connection-matrix RP track
(`Graph.FLS.main`) together with the cut-distance limit. We record it here as a single named axiom
and do not re-prove it. -/

/-- **Lovász–Szegedy representability** (the genuine graphon theorem: Lovász–Szegedy, *Limits of
dense graph sequences*, 2006 = Lovász, *Large Networks and Graph Limits*, 2012, Thm 5.54 / §5.6,
Thm 14.31). The `[0,1]` value bound `hb : IsBounded f` is essential — without it the multiplicative,
normalized, reflection-positive parameter `f F = 2 ^ (F.edgeFinset.card)` has `f K₂ = 2 ∉ [0,1]` and
is not graphon-realizable. (FLS JAMS 2007 Thm 2.4 is the DISTINCT finite-weighted *rank-bounded*
version with unbounded weights.) A TRUE classical theorem, absent from Mathlib;
owned/discharged in `reflection-positivity` (`Graph.FLS.main` + the cut-distance
limit). To be discharged. -/
axiom lovasz_szegedy_representability (f : GraphParam)
    (hm : IsMultiplicative f) (hn : IsNormalized f) (hrp : ReflectionPositive f) (hb : IsBounded f) :
    RealizedByGraphon f

/-! ## The easy (forward) direction

Every hom-density parameter `t(·, W)` is multiplicative, normalized and reflection-positive. -/

/-- The graph parameter attached to a graphon `W`: `homDensityParam W F = t(F, W)`. -/
noncomputable def homDensityParam (W : Graphon Ω μ) : GraphParam :=
  fun _V _ F => haveI := Classical.decRel F.Adj; homDensity F W

theorem homDensityParam_apply {V : Type} [Fintype V] (W : Graphon Ω μ) (F : SimpleGraph V)
    [DecidableRel F.Adj] : homDensityParam W F = homDensity F W := by
  unfold homDensityParam
  congr 1

/-- `t(·, W)` is multiplicative (reuses `homDensity_sum`). -/
theorem homDensityParam_isMultiplicative (W : Graphon Ω μ) :
    IsMultiplicative (homDensityParam W) := by
  intro V₁ V₂ _ _ F₁ F₂
  classical
  rw [homDensityParam_apply, homDensityParam_apply, homDensityParam_apply, homDensity_sum]

/-- `t(·, W)` is normalized: the empty graph on the empty type has hom density `1`. -/
theorem homDensityParam_isNormalized (W : Graphon Ω μ) :
    IsNormalized (homDensityParam W) := by
  classical
  rw [IsNormalized, homDensityParam_apply]
  -- `homDensity ⊥`: empty edge set ⇒ integrand `= 1`, and the product probability measure has
  -- total mass `1`.
  unfold homDensity homDensityIntegrand
  simp only [Finset.prod_of_isEmpty]
  rw [integral_const]
  simp

/-- `t(·, W)` is bounded: every hom density lies in `[0,1]` (`homDensity_mem_Icc`). -/
theorem homDensityParam_isBounded (W : Graphon Ω μ) :
    IsBounded (homDensityParam W) := by
  intro V _ F
  classical
  rw [homDensityParam_apply]
  exact Graphon.homDensity_mem_Icc F W

/-! ### Reflection positivity of `t(·, W)` via the Gram factorization

The connection matrix of hom densities is a **Gram matrix**. Writing a point of
`Fin k ⊕ (Fin m₁ ⊕ Fin m₂) → Ω` as `(y, z₁, z₂)` with `y : Fin k → Ω` the labels, the gluing
integrand factors (label-independence ⇒ the two edge sets are disjoint):

  `homDensityIntegrand (glue G₁ G₂) W (y,z₁,z₂)
      = homDensityIntegrand G₁ W (y,z₁) · homDensityIntegrand G₂ W (y,z₂)`.

Integrating over `z₁, z₂` (Fubini), `t(glue G₁ G₂, W) = ∫_y P G₁ y · P G₂ y dμ^k` where
`P G y := ∫_z homDensityIntegrand G W (y,z) dμ^m` is the **partial density**. The quadratic form is
then `∫_y (∑ᵢ cᵢ · P (G i) y)² ≥ 0`. -/

section Gram

variable {k : ℕ}

/-- `Sym2.map (glueInl …)` as an embedding. -/
def sym2GlueInlEmb (k m₁ m₂ : ℕ) : Sym2 (Fin k ⊕ Fin m₁) ↪ Sym2 (Fin k ⊕ (Fin m₁ ⊕ Fin m₂)) :=
  ⟨Sym2.map (glueInl k m₁ m₂), Sym2.map.injective (glueInl k m₁ m₂).injective⟩

/-- `Sym2.map (glueInr …)` as an embedding. -/
def sym2GlueInrEmb (k m₁ m₂ : ℕ) : Sym2 (Fin k ⊕ Fin m₂) ↪ Sym2 (Fin k ⊕ (Fin m₁ ⊕ Fin m₂)) :=
  ⟨Sym2.map (glueInr k m₁ m₂), Sym2.map.injective (glueInr k m₁ m₂).injective⟩

variable {m₁ m₂ : ℕ}

/-- `edgeVal` of a `glueInl`-mapped edge only depends on the `glueInl` coordinates of `x`. -/
theorem edgeVal_map_glueInl (W : Graphon Ω μ) (x : (Fin k ⊕ (Fin m₁ ⊕ Fin m₂)) → Ω)
    (e : Sym2 (Fin k ⊕ Fin m₁)) :
    edgeVal W x (Sym2.map (glueInl k m₁ m₂) e) = edgeVal W (x ∘ glueInl k m₁ m₂) e := by
  induction e with
  | _ a b => simp only [Sym2.map_mk, edgeVal, Sym2.lift_mk, Function.comp_apply]

/-- `edgeVal` of a `glueInr`-mapped edge only depends on the `glueInr` coordinates of `x`. -/
theorem edgeVal_map_glueInr (W : Graphon Ω μ) (x : (Fin k ⊕ (Fin m₁ ⊕ Fin m₂)) → Ω)
    (e : Sym2 (Fin k ⊕ Fin m₂)) :
    edgeVal W x (Sym2.map (glueInr k m₁ m₂) e) = edgeVal W (x ∘ glueInr k m₁ m₂) e := by
  induction e with
  | _ a b => simp only [Sym2.map_mk, edgeVal, Sym2.lift_mk, Function.comp_apply]

variable (G₁ : SimpleGraph (Fin k ⊕ Fin m₁)) (G₂ : SimpleGraph (Fin k ⊕ Fin m₂))
  [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]

noncomputable instance : DecidableRel (glue G₁ G₂).Adj := Classical.decRel _

omit [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] in
/-- Membership in the glued edge set: an edge is the `glueInl`-image of a `G₁`-edge or the
`glueInr`-image of a `G₂`-edge. -/
theorem mem_edgeSet_glue (e : Sym2 (Fin k ⊕ (Fin m₁ ⊕ Fin m₂))) :
    e ∈ (glue G₁ G₂).edgeSet ↔
      (∃ e₁ ∈ G₁.edgeSet, Sym2.map (glueInl k m₁ m₂) e₁ = e) ∨
        (∃ e₂ ∈ G₂.edgeSet, Sym2.map (glueInr k m₁ m₂) e₂ = e) := by
  induction e with
  | _ a b =>
    simp only [glue, SimpleGraph.mem_edgeSet, SimpleGraph.sup_adj, SimpleGraph.map_adj]
    constructor
    · rintro (⟨u, v, h, hu, hv⟩ | ⟨u, v, h, hu, hv⟩)
      · exact Or.inl ⟨s(u, v), h, by rw [Sym2.map_mk, hu, hv]⟩
      · exact Or.inr ⟨s(u, v), h, by rw [Sym2.map_mk, hu, hv]⟩
    · rintro (⟨e₁, he₁, heq⟩ | ⟨e₂, he₂, heq⟩)
      · induction e₁ with
        | _ u v =>
          rw [Sym2.map_mk, Sym2.eq_iff] at heq
          rcases heq with ⟨hu, hv⟩ | ⟨hu, hv⟩
          · exact Or.inl ⟨u, v, he₁, hu, hv⟩
          · exact Or.inl ⟨v, u, he₁.symm, hv, hu⟩
      · induction e₂ with
        | _ u v =>
          rw [Sym2.map_mk, Sym2.eq_iff] at heq
          rcases heq with ⟨hu, hv⟩ | ⟨hu, hv⟩
          · exact Or.inr ⟨u, v, he₂, hu, hv⟩
          · exact Or.inr ⟨v, u, he₂.symm, hv, hu⟩

/-- Under **label-independence** of both factors, the two image edge sets are disjoint as Finsets:
the only way a `glueInl`-image could coincide with a `glueInr`-image is via a label–label edge,
which independence forbids. -/
theorem disjoint_edgeFinset_glue (hG₁ : LabelIndependent G₁) (hG₂ : LabelIndependent G₂) :
    Disjoint (G₁.edgeFinset.map (sym2GlueInlEmb k m₁ m₂))
      (G₂.edgeFinset.map (sym2GlueInrEmb k m₁ m₂)) := by
  rw [Finset.disjoint_left]
  rintro e he₁ he₂
  rw [Finset.mem_map] at he₁ he₂
  obtain ⟨a, ha, hae⟩ := he₁
  obtain ⟨b, hb, hbe⟩ := he₂
  rw [← hae] at hbe
  simp only [sym2GlueInlEmb, sym2GlueInrEmb, Function.Embedding.coeFn_mk] at hbe
  rw [SimpleGraph.mem_edgeFinset] at ha hb
  -- Both endpoints of `a` must be labels (otherwise a body coordinate forces inl ≠ inr).
  induction a with
  | _ p q =>
    induction b with
    | _ r s =>
      simp only [Sym2.map_mk, Sym2.eq_iff, glueInl, glueInr, Function.Embedding.coeFn_mk] at hbe
      -- Case-split the four endpoints; only the all-labels subcase survives, contradicting hG₁.
      rcases p with p | p <;> rcases q with q | q <;> rcases r with r | r <;> rcases s with s | s <;>
        simp_all [Sum.map, LabelIndependent, SimpleGraph.mem_edgeSet]

/-- The glued edge `Finset` splits as the disjoint union of the `glueInl`/`glueInr` images of the
two factor edge sets (using label-independence for disjointness). -/
theorem edgeFinset_glue :
    (glue G₁ G₂).edgeFinset =
      (G₁.edgeFinset.map (sym2GlueInlEmb k m₁ m₂)) ∪ (G₂.edgeFinset.map (sym2GlueInrEmb k m₁ m₂)) := by
  classical
  ext e
  rw [Finset.mem_union, SimpleGraph.mem_edgeFinset, mem_edgeSet_glue]
  simp only [Finset.mem_map, SimpleGraph.mem_edgeFinset, sym2GlueInlEmb, sym2GlueInrEmb,
    Function.Embedding.coeFn_mk]

/-- The glued hom-density integrand factors as the product of the two factor integrands, the first
read off the `glueInl` coordinates of `x`, the second off the `glueInr` coordinates. -/
theorem homDensityIntegrand_glue (W : Graphon Ω μ)
    (hG₁ : LabelIndependent G₁) (hG₂ : LabelIndependent G₂)
    (x : (Fin k ⊕ (Fin m₁ ⊕ Fin m₂)) → Ω) :
    homDensityIntegrand (glue G₁ G₂) W x =
      homDensityIntegrand G₁ W (x ∘ glueInl k m₁ m₂) *
        homDensityIntegrand G₂ W (x ∘ glueInr k m₁ m₂) := by
  classical
  unfold homDensityIntegrand
  rw [edgeFinset_glue G₁ G₂, Finset.prod_union (disjoint_edgeFinset_glue G₁ G₂ hG₁ hG₂),
    Finset.prod_map, Finset.prod_map]
  congr 1
  · refine Finset.prod_congr rfl (fun e _ => ?_)
    simp only [sym2GlueInlEmb, Function.Embedding.coeFn_mk, edgeVal_map_glueInl]
  · refine Finset.prod_congr rfl (fun e _ => ?_)
    simp only [sym2GlueInrEmb, Function.Embedding.coeFn_mk, edgeVal_map_glueInr]

/-- The **partial hom density** of a `k`-labeled graph `G` with the labels fixed at `y : Fin k → Ω`:
integrate the hom-density integrand over the body `Fin m`, against `μ^{⊗ Fin m}`. -/
noncomputable def partialDensity {m : ℕ} (W : Graphon Ω μ) (G : SimpleGraph (Fin k ⊕ Fin m))
    [DecidableRel G.Adj] (y : Fin k → Ω) : ℝ :=
  ∫ z, homDensityIntegrand G W (Sum.elim y z) ∂(piMeasure (Fin m) μ)

omit [MeasurableSpace Ω] [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] in
/-- `x ∘ glueInl` is `Sum.elim` of the label coordinates and the first body coordinates of `x`. -/
theorem comp_glueInl (x : (Fin k ⊕ (Fin m₁ ⊕ Fin m₂)) → Ω) :
    x ∘ glueInl k m₁ m₂ = Sum.elim (fun a => x (Sum.inl a)) (fun p => x (Sum.inr (Sum.inl p))) := by
  funext v; rcases v with a | p <;> rfl

omit [MeasurableSpace Ω] [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] in
/-- `x ∘ glueInr` is `Sum.elim` of the label coordinates and the second body coordinates of `x`. -/
theorem comp_glueInr (x : (Fin k ⊕ (Fin m₁ ⊕ Fin m₂)) → Ω) :
    x ∘ glueInr k m₁ m₂ = Sum.elim (fun a => x (Sum.inl a)) (fun p => x (Sum.inr (Sum.inr p))) := by
  funext v; rcases v with a | p <;> rfl

/-- **Inner Fubini step.** With the labels `y` fixed, integrating the product of the two factor
integrands over the combined body `(Fin m₁ ⊕ Fin m₂) → Ω` factors as the product of the two partial
densities at `y`. -/
theorem integral_body_prod (W : Graphon Ω μ) (y : Fin k → Ω) :
    ∫ w : (Fin m₁ ⊕ Fin m₂) → Ω,
        homDensityIntegrand G₁ W (Sum.elim y (w ∘ Sum.inl)) *
          homDensityIntegrand G₂ W (Sum.elim y (w ∘ Sum.inr)) ∂(piMeasure (Fin m₁ ⊕ Fin m₂) μ)
      = partialDensity W G₁ y * partialDensity W G₂ y := by
  classical
  set e : ((Fin m₁ ⊕ Fin m₂) → Ω) ≃ᵐ ((Fin m₁ → Ω) × (Fin m₂ → Ω)) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ => Ω) with he
  have hmp : MeasurePreserving e (piMeasure (Fin m₁ ⊕ Fin m₂) μ)
      ((piMeasure (Fin m₁) μ).prod (piMeasure (Fin m₂) μ)) := by
    rw [piMeasure, piMeasure, piMeasure]
    exact measurePreserving_sumPiEquivProdPi (fun _ => μ)
  set g : (Fin m₁ → Ω) × (Fin m₂ → Ω) → ℝ := fun p =>
    homDensityIntegrand G₁ W (Sum.elim y p.1) * homDensityIntegrand G₂ W (Sum.elim y p.2) with hg
  have hfac : ∀ w : (Fin m₁ ⊕ Fin m₂) → Ω,
      homDensityIntegrand G₁ W (Sum.elim y (w ∘ Sum.inl)) *
          homDensityIntegrand G₂ W (Sum.elim y (w ∘ Sum.inr)) = g (e w) := by
    intro w
    simp [he, hg, MeasurableEquiv.sumPiEquivProdPi, Function.comp_def]
  calc ∫ w, homDensityIntegrand G₁ W (Sum.elim y (w ∘ Sum.inl)) *
          homDensityIntegrand G₂ W (Sum.elim y (w ∘ Sum.inr)) ∂(piMeasure (Fin m₁ ⊕ Fin m₂) μ)
      = ∫ w, g (e w) ∂(piMeasure (Fin m₁ ⊕ Fin m₂) μ) :=
        integral_congr_ae (ae_of_all _ hfac)
    _ = ∫ p, g p ∂((piMeasure (Fin m₁) μ).prod (piMeasure (Fin m₂) μ)) := hmp.integral_comp' g
    _ = partialDensity W G₁ y * partialDensity W G₂ y := by
        rw [hg]
        exact integral_prod_mul (fun z₁ => homDensityIntegrand G₁ W (Sum.elim y z₁))
          (fun z₂ => homDensityIntegrand G₂ W (Sum.elim y z₂))

/-- **Gram factorization of the glued hom density.** For label-independent factors,
`t(glue G₁ G₂, W) = ∫_y (partial density of G₁ at y) · (partial density of G₂ at y) dμ^k`. -/
theorem homDensity_glue (W : Graphon Ω μ)
    (hG₁ : LabelIndependent G₁) (hG₂ : LabelIndependent G₂) :
    homDensity (glue G₁ G₂) W =
      ∫ y : Fin k → Ω, partialDensity W G₁ y * partialDensity W G₂ y ∂(piMeasure (Fin k) μ) := by
  classical
  -- Split off the labels `Fin k` from the glued vertex set.
  set e : ((Fin k ⊕ (Fin m₁ ⊕ Fin m₂)) → Ω) ≃ᵐ
      ((Fin k → Ω) × ((Fin m₁ ⊕ Fin m₂) → Ω)) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ => Ω) with he
  have hmp : MeasurePreserving e (piMeasure (Fin k ⊕ (Fin m₁ ⊕ Fin m₂)) μ)
      ((piMeasure (Fin k) μ).prod (piMeasure (Fin m₁ ⊕ Fin m₂) μ)) := by
    rw [piMeasure, piMeasure, piMeasure]
    exact measurePreserving_sumPiEquivProdPi (fun _ => μ)
  -- The glued integrand, transported through `e`, becomes the product of factor integrands.
  set g : (Fin k → Ω) × ((Fin m₁ ⊕ Fin m₂) → Ω) → ℝ := fun p =>
    homDensityIntegrand G₁ W (Sum.elim p.1 (p.2 ∘ Sum.inl)) *
      homDensityIntegrand G₂ W (Sum.elim p.1 (p.2 ∘ Sum.inr)) with hg
  have hfac : ∀ x : (Fin k ⊕ (Fin m₁ ⊕ Fin m₂)) → Ω,
      homDensityIntegrand (glue G₁ G₂) W x = g (e x) := by
    intro x
    rw [homDensityIntegrand_glue G₁ G₂ W hG₁ hG₂, comp_glueInl, comp_glueInr]
    simp [he, hg, MeasurableEquiv.sumPiEquivProdPi, Function.comp_def]
  calc homDensity (glue G₁ G₂) W
      = ∫ x, g (e x) ∂(piMeasure (Fin k ⊕ (Fin m₁ ⊕ Fin m₂)) μ) := by
        rw [homDensity]; exact integral_congr_ae (ae_of_all _ hfac)
    _ = ∫ p, g p ∂((piMeasure (Fin k) μ).prod (piMeasure (Fin m₁ ⊕ Fin m₂) μ)) :=
        hmp.integral_comp' g
    _ = ∫ y, (∫ w, g (y, w) ∂(piMeasure (Fin m₁ ⊕ Fin m₂) μ)) ∂(piMeasure (Fin k) μ) := by
        refine integral_prod g ?_
        -- `g` is bounded in `[0,1]` and measurable, hence integrable on a probability measure.
        letI : MeasurableSpace (Fin k) := ⊤
        letI : MeasurableSpace (Fin m₁ ⊕ Fin m₂) := ⊤
        letI : MeasurableSpace (Fin k ⊕ Fin m₁) := ⊤
        letI : MeasurableSpace (Fin k ⊕ Fin m₂) := ⊤
        have hmeas1 : Measurable (fun p : (Fin k → Ω) × ((Fin m₁ ⊕ Fin m₂) → Ω) =>
            (Sum.elim p.1 (p.2 ∘ Sum.inl) : Fin k ⊕ Fin m₁ → Ω)) := by
          apply measurable_pi_lambda; rintro (a | a)
          · exact (measurable_pi_apply a).comp measurable_fst
          · exact (measurable_pi_apply (Sum.inl a)).comp measurable_snd
        have hmeas2 : Measurable (fun p : (Fin k → Ω) × ((Fin m₁ ⊕ Fin m₂) → Ω) =>
            (Sum.elim p.1 (p.2 ∘ Sum.inr) : Fin k ⊕ Fin m₂ → Ω)) := by
          apply measurable_pi_lambda; rintro (a | a)
          · exact (measurable_pi_apply a).comp measurable_fst
          · exact (measurable_pi_apply (Sum.inr a)).comp measurable_snd
        refine Integrable.mono' (integrable_const 1) ?_ (ae_of_all _ (fun p => ?_))
        · refine (Measurable.aestronglyMeasurable ?_)
          rw [hg]
          exact ((Graphon.measurable_homDensityIntegrand G₁ W).comp hmeas1).mul
            ((Graphon.measurable_homDensityIntegrand G₂ W).comp hmeas2)
        · rw [hg, Real.norm_of_nonneg (mul_nonneg (Graphon.homDensityIntegrand_nonneg G₁ W _)
            (Graphon.homDensityIntegrand_nonneg G₂ W _))]
          exact mul_le_one₀ (Graphon.homDensityIntegrand_le_one G₁ W _)
            (Graphon.homDensityIntegrand_nonneg G₂ W _) (Graphon.homDensityIntegrand_le_one G₂ W _)
    _ = ∫ y, partialDensity W G₁ y * partialDensity W G₂ y ∂(piMeasure (Fin k) μ) := by
        refine integral_congr_ae (ae_of_all _ (fun y => ?_))
        rw [hg]; exact integral_body_prod G₁ G₂ W y

omit [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] in
/-- The partial density is measurable in the label point `y`. -/
theorem measurable_partialDensity {m : ℕ} (W : Graphon Ω μ) (G : SimpleGraph (Fin k ⊕ Fin m))
    [DecidableRel G.Adj] : Measurable (partialDensity W G) := by
  letI : MeasurableSpace (Fin k) := ⊤
  letI : MeasurableSpace (Fin m) := ⊤
  letI : MeasurableSpace (Fin k ⊕ Fin m) := ⊤
  unfold partialDensity
  have hint : Measurable (fun p : (Fin k → Ω) × (Fin m → Ω) =>
      homDensityIntegrand G W (Sum.elim p.1 p.2)) := by
    refine (Graphon.measurable_homDensityIntegrand G W).comp ?_
    apply measurable_pi_lambda; rintro (a | a)
    · exact (measurable_pi_apply a).comp measurable_fst
    · exact (measurable_pi_apply a).comp measurable_snd
  exact (MeasureTheory.StronglyMeasurable.integral_prod_right'
    (ν := piMeasure (Fin m) μ) hint.stronglyMeasurable).measurable

omit [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] in
/-- The partial density lies in `[0,1]`. -/
theorem partialDensity_mem_Icc {m : ℕ} (W : Graphon Ω μ) (G : SimpleGraph (Fin k ⊕ Fin m))
    [DecidableRel G.Adj] (y : Fin k → Ω) : partialDensity W G y ∈ Set.Icc (0:ℝ) 1 := by
  letI : MeasurableSpace (Fin m) := ⊤
  haveI : MeasurableSingletonClass (Fin m) := ⟨fun _ => trivial⟩
  refine ⟨integral_nonneg fun z => Graphon.homDensityIntegrand_nonneg G W _, ?_⟩
  calc partialDensity W G y
      ≤ ∫ _ : Fin m → Ω, (1:ℝ) ∂(piMeasure (Fin m) μ) := by
        refine integral_mono ?_ (integrable_const 1)
          (fun z => Graphon.homDensityIntegrand_le_one G W _)
        have hmz : Measurable (fun z : Fin m → Ω => (Sum.elim y z : Fin k ⊕ Fin m → Ω)) := by
          apply measurable_pi_lambda; rintro (a | a)
          · exact measurable_const
          · exact measurable_pi_apply a
        refine Integrable.mono' (integrable_const 1)
          ((Graphon.measurable_homDensityIntegrand G W).comp hmz).aestronglyMeasurable
          (ae_of_all _ (fun z => ?_))
        rw [Real.norm_of_nonneg (Graphon.homDensityIntegrand_nonneg G W _)]
        exact Graphon.homDensityIntegrand_le_one G W _
    _ = 1 := by rw [integral_const]; simp

omit [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] in
/-- The partial density is integrable in the label point. -/
theorem integrable_partialDensity {m : ℕ} (W : Graphon Ω μ) (G : SimpleGraph (Fin k ⊕ Fin m))
    [DecidableRel G.Adj] : Integrable (partialDensity W G) (piMeasure (Fin k) μ) := by
  refine Integrable.mono' (integrable_const 1)
    (measurable_partialDensity W G).aestronglyMeasurable (ae_of_all _ (fun y => ?_))
  rw [Real.norm_of_nonneg (partialDensity_mem_Icc W G y).1]
  exact (partialDensity_mem_Icc W G y).2

end Gram

/-- `t(·, W)` is **reflection-positive**: each connection matrix of hom densities is a Gram matrix,
so its quadratic form `∑ᵢⱼ cᵢcⱼ t(Gᵢ ⊙ Gⱼ, W) = ∫_y (∑ᵢ cᵢ · Pᵢ(y))² dμ^k ≥ 0`. -/
theorem homDensityParam_isReflectionPositive (W : Graphon Ω μ) :
    ReflectionPositive (homDensityParam W) := by
  classical
  intro k ι _ m G hG c
  set P : ι → (Fin k → Ω) → ℝ := fun i => partialDensity W (G i) with hP
  -- Each term `fun y => c i * c j * (P i y * P j y)` is integrable (bounded, finite measure).
  have hPbdd : ∀ i (y : Fin k → Ω), |P i y| ≤ 1 := fun i y => by
    rw [abs_of_nonneg (partialDensity_mem_Icc W (G i) y).1]
    exact (partialDensity_mem_Icc W (G i) y).2
  have hint : ∀ i j, Integrable (fun y => c i * c j * (P i y * P j y)) (piMeasure (Fin k) μ) := by
    intro i j
    refine Integrable.mono' (integrable_const (|c i| * |c j| * 1)) ?_ (ae_of_all _ (fun y => ?_))
    · exact (((measurable_partialDensity W (G i)).mul
        (measurable_partialDensity W (G j))).const_mul _).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      have hPP : |P i y| * |P j y| ≤ 1 := mul_le_one₀ (hPbdd i y) (abs_nonneg _) (hPbdd j y)
      gcongr
  -- Rewrite each entry as the Gram integral, then pull the double sum inside.
  have hentry : ∀ i j, homDensityParam W (glue (G i) (G j)) =
      ∫ y, P i y * P j y ∂(piMeasure (Fin k) μ) := by
    intro i j
    rw [homDensityParam_apply, homDensity_glue (G i) (G j) W (hG i) (hG j)]
  calc (0:ℝ)
      ≤ ∫ y, (∑ i, c i * P i y) ^ 2 ∂(piMeasure (Fin k) μ) :=
        integral_nonneg (fun y => sq_nonneg _)
    _ = ∑ i, ∑ j, c i * c j * ∫ y, P i y * P j y ∂(piMeasure (Fin k) μ) := by
        rw [show (fun y => (∑ i, c i * P i y) ^ 2)
            = (fun y => ∑ i, ∑ j, c i * c j * (P i y * P j y)) from by
          funext y
          rw [sq, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))]
        rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [integral_finsetSum _ (fun j _ => hint i j)]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [integral_const_mul]
    _ = ∑ i, ∑ j, c i * c j * homDensityParam W (glue (G i) (G j)) := by
        simp_rw [hentry]

/-- A realized parameter coincides with the hom-density parameter of its witnessing graphon. -/
theorem eq_homDensityParam_of_realized {f : GraphParam} {W : Graphon ℝ unitMeasure}
    (hW : ∀ {V : Type} [Fintype V] (F : SimpleGraph V),
      f F = haveI := Classical.decRel F.Adj; homDensity F W) :
    f = homDensityParam W := by
  funext V _ F
  classical
  rw [hW F, homDensityParam_apply]

/-! ## The representability theorem -/

/-- **Graphon representability (Lovász–Szegedy)**, Tier-C item 4.

A graph parameter `f` is realized by a graphon (`f = t(·, W)` for some graphon `W` over the unit
interval) **iff** it is multiplicative, normalized, reflection-positive, **and `[0,1]`-bounded**.

* Forward (⇒): PROVED here — `t(·, W)` is multiplicative (`homDensity_sum`), normalized (empty
  graph), reflection-positive (the connection matrix is a Gram matrix; `homDensity_glue`), and
  bounded (`homDensity_mem_Icc`).
* Converse (⇐): the single named axiom `lovasz_szegedy_representability` (the genuine Lovász–Szegedy
  graphon theorem, requiring the `[0,1]` value bound; cf. Lovász 2012 Thm 5.54), owned by
  `reflection-positivity`. The boundedness hypothesis is essential: without it
  `f F = 2 ^ (F.edgeFinset.card)` satisfies the other three but has `f K₂ = 2 ∉ [0,1]`. -/
theorem representability (f : GraphParam) :
    RealizedByGraphon f ↔
      (IsMultiplicative f ∧ IsNormalized f ∧ ReflectionPositive f ∧ IsBounded f) := by
  constructor
  · rintro ⟨W, hW⟩
    have hf : f = homDensityParam W := eq_homDensityParam_of_realized hW
    subst hf
    exact ⟨homDensityParam_isMultiplicative W, homDensityParam_isNormalized W,
      homDensityParam_isReflectionPositive W, homDensityParam_isBounded W⟩
  · rintro ⟨hm, hn, hrp, hb⟩
    exact lovasz_szegedy_representability f hm hn hrp hb

end Graphons
