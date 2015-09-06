/*
 * Copyright (c) 2015 Lutz Hofmann
 * Licensed under the MIT license, see LICENSE.txt for details.
 */

AttachSpec("lib/buildings.spec");
SetAssertions(1);
SetVerbose("buildingLib", true);
SetVerbose("buildingQuotient", true);
SetVerbose("harmonicCochains", true);

// parameters for quotient building
d := 2;
q := 2;
K := GF(q);
R<T> := PolynomialRing(K);
N := T^2 + T + 1;

// list of polynomials for which Hecke operators will be computed
polynomials := &cat[ SetToSequence(AllIrreduciblePolynomials(K, deg)) : deg in [1..6] ];
polynomials := [ P : P in polynomials | GCD(N, P) eq 1 ];



logfile := Sprintf("log/HARMONIC_D~%o_Q~%o_N~%o.log", d, q, R ! N);
SetLogFile(logfile);

printf "\n[*] Computing quotient building for d=%o, q=%o, N=%o.\n\n", d, q, R ! N;
time quotient := QuotientGamma0N(d, N : additionalLevels := 1);

nonSimplicialData := QuotientNonSimplicialData(quotient);
if #nonSimplicialData eq 0 then
    print "Quotient is simplicial.";
else
    print "Non-simplicial gluing data: ", nonSimplicialData;
end if;

print "\n[*] Computing space of harmonic cochains.\n";
_, compact := QuotientCusp(quotient);
compactSubQuotient := InducedSubQuotient(quotient, compact);
time harmonicSpace := HarmonicCochainSpace(compactSubQuotient);

print "Dim H!:", harDimension(harmonicSpace);
print "Basis:", harmonicSpace`basis;

procedure Hecke(reps, harmonicSpace)    
    try
        transformationMatrix := harDoubleCosetOperator(harmonicSpace, reps : Precision := 200);
        print "Transformation matrix:", transformationMatrix;
        charPoly := CharacteristicPolynomial(transformationMatrix);    
        parent := Parent(charPoly); 
        AssignNames(~charPoly, ["T"]);
        print "Characteristic polynomial:", charPoly;
    catch e
        print "*** ERROR COMPUTING HECKE OPERATOR ***";
    end try;
end procedure;

for P in polynomials do
    printf "\n[*] Computing Hecke operator for k = 1, P = %o.\n\n", P;
    time Hecke(HeckeLeftCosets(P, d, 1), harmonicSpace);
    if d eq 2 then
        printf "\n[*] Computing Hecke operator for k = 2, P = %o.\n\n", P;
        time Hecke(HeckeLeftCosets(P, d, 2), harmonicSpace);
    end if;
end for;
