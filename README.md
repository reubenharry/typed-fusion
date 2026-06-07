# Quantum Many Body physics using basis-free linear algebra

This project contains various experiments using linearmap-category to write quantum many body physics code, in particular tensor network algorithms.

The motivating goal is to write a classic and standard algorithm, the Density Matrix Renormalization Group (DMRG), with the following features:

- actual basis free tensors, not arrays
- symmetry aware (code can handle intertwining maps between representations)
- (possibly)typed version of ITensor array contraction
- (possibly) handling for tensor products of finite and infinite systems with laziness

## Roadmap

To get there, I need the following:

- support for complex numbers in linearmap-category (mostly done)
- support for Irreps on top of linearmap-category (underway)
- implementation of SVD (started - currently I just use hmatrix, but want to upgrade to a basis-free implementation)
- an MPS implementation (two designs being considered, depends whether I want them to form a vector space or fibre bundle)
- the move step of the DMRG algorithm (partly done - I understand how to do it)
- implementation of the solve step of DMRG (underway)


