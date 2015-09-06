/*
 * Copyright (c) 2015 Lutz Hofmann
 * Licensed under the MIT license, see LICENSE.txt for details.
 */

AttachSpec("lib/buildings.spec");
import "lib/buildingQuotient.m" : QuotientBuildingRec;
import "lib/buildingLib.m" : LaurentEqual, PolynomialsUptoDegree;

// optional dependencies
FctsForTheGraph_FOUND := false;
Dim1Hecke_FOUND := false;
try
    Attach("optional_dependencies/FctsForTheGraph.mg");
    FctsForTheGraph_FOUND := true;
    Attach("optional_dependencies/AuxiliaryFcts.mg");
    Attach("optional_dependencies/CongruenceSubgroups.mg");
    Attach("optional_dependencies/QuotientGraphExtended.mg");
    Attach("optional_dependencies/ForHomology.mg");
    Dim1Hecke_FOUND := true;
catch e
    forward decom;
    forward CreateQuotientGraph;
    forward MatrixHO;
    print("Please ignore above error message. See folder optional_dependencies for more information.\n");
end try;


SetAssertions(3);
SetVerbose("buildingLib", true);
SetVerbose("buildingQuotient", true);
SetVerbose("harmonicCochains", true);

procedure testPassed(name)
    printf "*** test %o passed ***\n", name;
end procedure;

function RandomKinf(Kinf, valuation, degree)
    K := BaseRing(Kinf);
    coefficients := [Random(K) : i in [1..degree-valuation]];
    return elt<Kinf| valuation, coefficients, -1>;
end function;

function RandomGLKinf(Kinf, d, valuation, degree)
    repeat
        M := Matrix(Kinf, d+1, d+1, [RandomKinf(Kinf, valuation, degree) : i in [1..(d+1)*(d+1)]]);
    until IsInvertible(M);
    return M;
end function;

function RandomPolynomial(K, degree : Nonzero := false)
    repeat
        P := PolynomialRing(K) ! [Random(K) : i in [1..degree+1]];
    until not Nonzero or not IsZero(P);
    return P;
end function;

function RandomGamma0(K, d, degree)
    R := PolynomialRing(K);
    repeat
        M := Matrix(R, d+1, d+1, [R| RandomPolynomial(K, Random(-1, degree)) : i in [1..(d+1)*(d+1)] ]);
    until IsInvertible(M);
    return M;    
end function;

function RandomSLMod(K, N, d, degree)
    R := PolynomialRing(K);
    repeat
        M := Matrix(R, d+1, d+1, [R| RandomPolynomial(K, Random(-1, degree)) : i in [1..(d+1)*(d+1)] ]);
    until Determinant(M) mod N eq 1;
    return M;    
end function;

function RandomGLFrac(K, d, numerator, denominator) 
    Quot := FieldOfFractions(PolynomialRing(K));
    repeat
        M := Matrix(Quot, d+1, d+1, 
                    [Quot| RandomPolynomial(K, numerator) / RandomPolynomial(K, denominator : Nonzero := true) 
                     : i in [1..(d+1)*(d+1)] ]);
    until IsInvertible(M);
    return M;
end function;

function TreeRepr(n, Kinf)
    if n lt 0 then
        return Matrix(Kinf, 2, 2, [0, 1, Kinf.1^-n, 0]);
    else
        return Matrix(Kinf, 2, 2, [1, 0, 0, Kinf.1^n]);
    end if;
end function;


/*
    UNIT TESTS
*/

procedure test_sl_lift_impl(q, N, d)
    K := GF(q);
    for i in [1..100] do
        M := RandomSLMod(K, N, d, Degree(N)-1);
        lift := LiftSLMod(M, N);
        assert Determinant(lift) eq 1;        
        assert &and[ (M[i,j] mod N) eq (lift[i,j] mod N) : i,j in [1..d+1] ];
    end for;
end procedure;

procedure test_sl_lift()
    for d in [1,2,3,4] do
        for q in [2,3,4,5,8] do
            K := GF(q);
            R<T> := PolynomialRing(K);
            N := R ! T;
            test_sl_lift_impl(q,N,d);            
            N := R ! T^3;
            test_sl_lift_impl(q,N,d);
            N := R ! T^2 + T;
            test_sl_lift_impl(q,N,d);
        end for;
        testPassed(Sprintf("SL lift d=%o", d));
    end for;
end procedure;

procedure test_decom_dim_1_impl(q)
    K := GF(q);
    R<T> := PolynomialRing(K);

    Kinf<pi> := LaurentSeriesRing(K : Precision := 200);
    PI := UniformizingElement(Kinf);

    Quot := FieldOfFractions(R);
    incl := hom< Quot -> Kinf | Kinf.1^-1 >;

    for i in [1..100] do
        M := RandomGLFrac(K, 1, 10, 50);

        dec := decom(M,K,R);
        g0,simplex0,h0,alpha0,_,n0 := Explode(dec);
        g,simplex,h,alpha := WeylChamberSimplexDecomposition(ChangeRing(M, incl));
        g := g^-1;

        assert TreeRepr(n0, Kinf) eq WeylChamberSimplexToMatrix(simplex, Kinf);

        fixgrp := Gamma0SimplexFixgroupTemplate(simplex);
        assert &and[ m[i,j] eq 0 or Degree(m[i,j]) le fixgrp[i,j] where m is g^-1 * g0 : i,j in [1..2] ];
    end for;

    testPassed(Sprintf("decom d=1 q=%o",q));
end procedure;

procedure test_decom_dim_1()
    if not FctsForTheGraph_FOUND then
        print "Skipping test decom d=1 (dependencies not found).";
        return;
    end if;

    for q in [2,3,4,5,8,9] do
        test_decom_dim_1_impl(q);        
    end for;
end procedure;

procedure test_decom_dim_2_impl(q)
    K := GF(q);
    R<T> := PolynomialRing(K);
    Kinf<pi> := LaurentSeriesRing(K : Precision := 200);

    for i in [1..100] do
        M := RandomGLKinf(Kinf, 2, -10, 50);
        g,simplex,h,alpha := WeylChamberSimplexDecomposition(M);
        assert LaurentEqual(PolynomialMatrixToLaurent(g, Kinf) * M * h * alpha, WeylChamberSimplexToMatrix(simplex, Kinf) : epsilon := 15);
    end for;

    testPassed(Sprintf("decom d=2 q=%o",q));
end procedure;

procedure test_decom_dim_2()
    for q in [2,3,4,5,8,9] do
        test_decom_dim_2_impl(q);        
    end for;
end procedure;

procedure test_all_polynomials()
    for q in [2,3,4,5,8,9] do
        for deg in [-5,-1,0,1,2,5] do
            polynomials := PolynomialsUptoDegree(q, deg);

            assert #polynomials eq #Set(polynomials);
            assert #polynomials eq (deg lt 0 select 1 else q^(deg+1));
            assert &and[ IsZero(p) or Degree(p) le deg : p in polynomials ];
        end for;
    end for;
    testPassed("PolynomialsUptoDegree");
end procedure;

procedure test_hecke_representatives_impl(d, q, N, degP, k)
    K := GF(q);
    R<T> := PolynomialRing(K);
    Quot := FieldOfFractions(R);
    N := R ! N;
    repeat
        P := RandomIrreduciblePolynomial(K, degP);
    until GCD(P, N) eq 1;    
    cosets := HeckeLeftCosets(P, d, k);

    repeat
        g := RandomGamma0(K, d, 5);        
    until IsGamma0NElement(g, N);
    g := ChangeRing(g, Quot);
    cosetsg := [ h*g : h in cosets ];
    for j := 1 to #cosetsg do
        found := false;
        for k := 1 to #cosets do
            if not found then                    
                h := cosetsg[j] * cosets[k]^-1;
                if CanChangeRing(h, R) and IsGamma0NElement(ChangeRing(h, R), N) then
                    cosetsg[j] := cosets[k];
                    found := true;
                end if;                
            end if;
        end for;
        if not found then
            printf "g=%o\n", g;
            printf "P=%o\n", P;
            printf "N=%o\n", N;
            assert false;
        end if;  
    end for;

    if not Set(cosetsg) eq Set(cosets) then
        printf "g=%o\n", g;
        printf "P=%o\n", P;
        printf "N=%o\n", N;            
        print "Translated:", #Set(cosetsg);
        print "Original:", #Set(cosets);
        assert false;
    end if;    
end procedure;

procedure test_hecke_representatives()
    for q in [2,3] do
        R<T> := PolynomialRing(GF(q));
        N := R ! T^2;
        for degP in [1,2,3,4,5] do
            test_hecke_representatives_impl(1, q, N, degP, 1);
        end for;
        testPassed(Sprintf("hecke representatives d=1 q=%o, N=%o", q, N));
    end for;    

    for q in [2,3] do
        R<T> := PolynomialRing(GF(q));
        N := R ! T^2;
        for degP in [1,2,3] do
            for k in [1,2] do
                test_hecke_representatives_impl(2, q, N, degP, k);
            end for;
        end for;
        testPassed(Sprintf("hecke representatives d=2 q=%o, N=%o", q, N));
    end for;    
end procedure;


// TODO:
//   Implement quotients of Gamma0 fixgroups
//   The following implementation of Gamma0FixgroupQuotient is incomplete, but tests are already in place
//
//   See also TODO in QuotientAddSimplex in buildingQuotient.m

function Gamma0FixgroupQuotient(q, otherFixgroup, fixgroup)
    assert Gamma0SubgroupIsContained(otherFixgroup, fixgroup);

    n := NumberOfRows(otherFixgroup);

    K := GF(q);
    R := PolynomialRing(K);

    difference := Matrix(Integers(),n,n,[]);
    for i := 1 to n do
        for j := 1 to n do
            if otherFixgroup[i,j] lt 0 then
                difference[i,j] := fixgroup[i,j];
            elif fixgroup[i,j]-otherFixgroup[i,j] gt 0 then
                difference[i,j] := fixgroup[i,j]-otherFixgroup[i,j]-1;
            else
                difference[i,j] := -1;
            end if;
        end for;
    end for;

    quot := AllMatricesFromTemplate(q, difference : CheckInvertible := false );
        
    for i := 1 to NumberOfRows(fixgroup) do
        for j := 1 to NumberOfColumns(fixgroup) do
            if difference[i,j] ge 0 then
                for k in [1..#quot] do
                    quot[k][i,j] *:= R.1^(otherFixgroup[i,j]+1);
                end for;
            end if;
        end for;
    end for;                

    quot := [ IdentityMatrix(R,n) + A : A in quot ];
    
    for i := 1 to n do
        for j := 1 to n do
            if i gt j and difference[i,j] ge 0 then
                permutation := [1..n];
                permutation[i] := j;
                permutation[j] := i;
                quot cat:= [ PermutationMatrix(R, permutation) ];
            end if;
        end for;
    end for;     

    return quot;
end function;


procedure test_fixgroup_quotients_impl(q, simplex1, simplex2)    
    d := #simplex1[1];
    K := GF(q);
    R<T> := PolynomialRing(K);

    fixgrpSmall := Gamma0SimplexFixgroupTemplate(simplex1);
    fixgrpSmallList := Gamma0SubgroupFromTemplate(q, fixgrpSmall);

    fixgrpBig := Gamma0SimplexFixgroupTemplate(simplex2);
    fixgrpBigList := Gamma0SubgroupFromTemplate(q, fixgrpBig);

    groupIndex := #fixgrpBigList / #fixgrpSmallList;

    quot := Gamma0FixgroupQuotient(q, fixgrpSmall, fixgrpBig);
    
    if #quot gt 1 then
        SetVerbose("buildingLib", false);
        cond := func< A | A in fixgrpSmallList >;
        cosets := CongruenceSubgroupDoubleCosets(cond, quot, [], [IdentityMatrix(R, d+1)], "left");
        SetVerbose("buildingLib", true);
        print #cosets;
        assert groupIndex eq #cosets;
    else
        assert groupIndex eq #quot;
    end if;    
end procedure;

procedure test_fixgroup_quotients()
    // TODO add more test cases
    test_fixgroup_quotients_impl(3, [<1,1>,<0,1>,<0,0>], [<0,1>,<1,1>]);
    test_fixgroup_quotients_impl(3, [<1,1>,<1,2>,<2,2>], [<2,2>]);
    testPassed("Gamma_0 fixgroup quotients");
end procedure;


procedure test_hecke_dim_1()
    if not Dim1Hecke_FOUND then
        print "Skipping test Hecke d=1 (dependencies not found).";
        return;
    end if;
    print "*** Testing my implementation against Yamidt's...";

    q := 2;
    K := GF(q);
    R<T> := PolynomialRing(K);
    N := T^3;

    polynomials := &cat[ SetToSequence(AllIrreduciblePolynomials(K, deg)) : deg in [1..3] ];
    polynomials := [ P : P in polynomials | GCD(N, P) eq 1 ];

    quotient_yamidt := CreateQuotientGraph(R,N,1,4);

    SetVerbose("buildingQuotient", false);
    quotient := QuotientGamma0N(1, N);
    compactSubQuotient := InducedSubQuotient(quotient, compact) where _, compact is QuotientCusp(quotient);
    harmonicSpace := HarmonicCochainSpace(compactSubQuotient);      
    SetVerbose("buildingQuotient", true);

    for P in polynomials do
        hecke := harDoubleCosetOperator(harmonicSpace, HeckeLeftCosets(P, 1, 1) : Precision := 200);
        my_charpoly := CharacteristicPolynomial(hecke);
        yamidt_charpoly := CharacteristicPolynomial(MatrixHO(quotient_yamidt, P));
        assert my_charpoly eq yamidt_charpoly;
    end for;

    testPassed("Hecke d=1");
end procedure;


/*
    TEST MAIN
*/

test_hecke_dim_1();
test_sl_lift();
test_decom_dim_1();
test_decom_dim_2();
test_all_polynomials();
test_hecke_representatives();

// TODO
//test_fixgroup_quotients();

print "*** all tests passed ***";
