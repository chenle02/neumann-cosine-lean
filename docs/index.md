---
title: "Neumann Cosine"
permalink: /
description: "Neumann cosine series on an interval and the discrete Neumann Laplacian, formalized in Lean 4 with Mathlib."
---

<section class="hero">
<p class="eyebrow">Lean 4 / Mathlib library · release v0.1.0 · Apache-2.0</p>
<h1>Neumann Cosine</h1>
<img class="banner" src="{{ '/assets/banner.svg' | relative_url }}" alt="The first three cosine modes on an interval, each with zero slope at both ends">
</section>

Neumann cosine series on an interval $`[0,L]`$ and the discrete Neumann Laplacian: orthogonality, product integrals, summable coefficients and pointwise expansions under $`W^{2,1}`$ or $`H^2`$ Neumann data, and convergence of the discrete spectrum. Formalized in Lean 4 with Mathlib.

<p class="actions"><a class="button" href="{{ '/what-is-proved.html' | relative_url }}">What is proved</a> <a class="button secondary" href="{{ '/verification.html' | relative_url }}">All Lean statements</a> <a class="button secondary" href="{{ '/getting-started.html' | relative_url }}">Get started</a></p>

<div class="boundary" markdown="1">
**Not proved here.**
- No PDE theory: no existence, uniqueness or regularity theorem for any differential equation, and no semigroup.
- No $`L^2`$ theory: completeness of the cosine system in $`L^2(0,L)`$ and Parseval's identity for general $`L^2`$ functions are not proved. The expansions above need summable coefficients, which the library derives from $`W^{2,1}`$ or $`H^2`$ Neumann data.
- No general bridge to Mathlib's `fourierCoeff`. `Coefficients.fourierCoeff_evenPeriodic` covers only the even $`2L`$-periodic extension of a `NeumannW21` function. A bridge for general integrable functions is planned for v0.2.
- One dimension only: no domains in two or more dimensions.
</div>

## Find your way

### Results

<div class="cards">
<div class="card"><h4><a href="{{ '/what-is-proved.html' | relative_url }}">What is proved</a></h4><p>Each result with its exact compared Lean statement.</p></div>
<div class="card"><h4><a href="{{ '/verification.html' | relative_url }}">All Lean statements</a></h4><p>Generated page: every result, its hypotheses, receipts and the checks that ran.</p></div>
<div class="card"><h4><a href="{{ '/coverage.html' | relative_url }}">Coverage table</a></h4><p>Every coverage row, its claims, inputs and notes.</p></div>
<div class="card"><h4><a href="{{ '/modules.html' | relative_url }}">Modules</a></h4><p>What each Lean module contains.</p></div>
</div>

### Use and trust

<div class="cards">
<div class="card"><h4><a href="{{ '/getting-started.html' | relative_url }}">Get started</a></h4><p>Build, verify, and depend on the library from your own Lake project.</p></div>
<div class="card"><h4><a href="{{ '/getting-started.html#trust-and-axioms' | relative_url }}">Trust and axioms</a></h4><p>Permitted axioms and what the comparator checks.</p></div>
<div class="card"><h4><a href="{{ '/acknowledgments.html' | relative_url }}">Acknowledgments and citation</a></h4><p>Authors and AI disclosure, lean-pkg, the Auburn University Easley Cluster, what it builds on, related work, and how to cite.</p></div>
</div>

## Related

This library was first developed for the [Chemotaxis III Lean companion](https://chenle02.github.io/chemotaxis-paper-iii-lean/). Its sibling library is [scalar-pitchfork-lean](https://chenle02.github.io/scalar-pitchfork-lean/). The two libraries are independent.
