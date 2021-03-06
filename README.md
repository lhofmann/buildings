# Quotient Buildings

A MAGMA framework for computing quotients of Bruhat-Tits buildings over function fields modulo congruence subgroups
and their Hecke operators.

This is the source code of algorithms developed in my Master's thesis [Algorithmen zur Berechnung arithmetischer Quotienten von Bruhat-Tits-Gebäuden zu PGL_d+1(K_inf)](thesis.pdf) (available in German only). Example output can be found in Chapter 5.

## Usage

See the examples `building.m` and `harmonic.m` for basic usage of this framework. 
They contain complete programs to compute quotient buildings and Hecke operators respectively 
for the congruence subgroup Gamma_0(N). If you only want to run computations, adjust the parameters
within these files and run `magma building.m` or `magma harmonic.m` respectively.

The scripts `log2tex.py` and `log2txt.py` convert logs generated by `harmonic.m` into the respective formats.
They are expected to be run inside directory `lib`.

#### Custom congruence subgroups

It is also possible to use this framework to compute quotients modulo arbitrary congruence subgroups.
Refer to the implementation of `QuotientGamma0N` and the definition of `QuotientBuildingRec` in `lib/buildingQuotient.m` 
for how to achieve this. You will need to adjust the creation of the `QuotientBuildingRec` structure as follows:

* Mandatory fields are `representatives`, `q`, `d`, `N` and `subgroupCondition`. 
* If you also provide `reductionFunc`, the computation of the quotient building will be much faster.
Hecke operatores are not implemented in the case where this function is missing.

#### Higher dimensions

For dimensions `d` greater than `2`, the following functions need minor adjustments:

`QuotientCusp`, `PermutationsAtVertex`, `HeckeLeftCosets`.

## Unit Tests

Run unit tests using `magma unit_tests.m`. Some of those will use optional dependencies if available, see folder
`optional_dependencies` for detail.

## Precomputed examples

The folder `examples` contains some precomputed tables of Hecke operators, in plain-text and LaTeX format. 
However, only the LaTeX files contain characteristic polynomials factorized into irreducibles.

## Dependencies

* code was tested using Magma V2.21-4
* JavaView: http://javaview.de/ (for visualising 2-dimensional quotients)
* GraphViz: http://www.graphviz.org/ (for visualising 1-dimensional quotients)
* The script `spring_layout.py` needs NetworkX (https://networkx.github.io) installed. It is invoked by `QuotientToJavaView` in `buildingQuotient.m` if parameter `Python` is set to `true`. 
