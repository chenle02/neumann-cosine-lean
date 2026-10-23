---
title: "Modules"
description: "The Lean modules of neumann-cosine-lean and what each contains."
---

# Modules

The library root imports every module below.

| Module | Contents |
|---|---|
| `NeumannCosine.Basic` | The mode, its frequency, orthogonality and Gram values |
| `NeumannCosine.Series.TermwiseIntegral` | Termwise integration of $`\ell^1`$ cosine series |
| `NeumannCosine.Series.Products` | Products of $`\ell^1`$ cosine series, interchange with the integral, signed-index reindexing |
| `NeumannCosine.KernelIntegrals` | Closed forms of integrals of products of three and four modes |
| `NeumannCosine.ProductIdentities` | Integrals of products of two to four cosine series as constrained convolutions |
| `NeumannCosine.Coefficients` | The class `NeumannW21`: $`O(k^{-2})`$ coefficients, summability, pointwise expansion |
| `NeumannCosine.Sobolev.WeakDerivative` | Weak derivatives on $`(0,L)`$, du Bois-Reymond, absolutely continuous representative |
| `NeumannCosine.Sobolev.H2Neumann` | $`H^2(0,L)`$ with Neumann trace lies in `NeumannW21` |
| `NeumannCosine.DivergenceFormProjection` | $`\lvert\int_0^L(R_0+R_1')\cos(k\pi x/L)\,dx\rvert\le(L+k\pi)B`$ when $`\lvert R_0\rvert,\lvert R_1\rvert\le B`$ on $`[0,L]`$, $`R_0`$ is integrable, $`R_1`$ is absolutely continuous on $`[0,L]`$ (or continuous on $`[0,L]`$ and differentiable at every point of $`(0,L)`$ with integrable derivative), and $`R_1(0)=R_1(L)=0`$ |
| `NeumannCosine.Discrete.Eigenvalues` | Discrete and continuum eigenvalues, $`\operatorname{sinc}^2`$ relation, convergence, lower bound |
| `NeumannCosine.Discrete.Laplacian` | The reflected three-point stencil on `Fin (N + 1)`, its cosine eigenvectors and basis |
| `NeumannCosine.Discrete.ModalMinimumTail` | One tail cutoff for all fine meshes, for a linearly coercive $`f`$ |
| `NeumannCosine.Discrete.ModalMinimumLimit` | The discrete modal minimum converges to the continuum infimum |
