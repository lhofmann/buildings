/*
 * Copyright (c) 2015 Lutz Hofmann
 * Licensed under the MIT license, see LICENSE.txt for details.
 */

freeze;
import "buildingLib.m" : PolynomialsUptoDegree, IndexListAddOne;

function ProjectivePrimarySpace(d, N)
    // N = P^k

    P := Factorization(N)[1][1];
    k := Factorization(N)[1][2];

    R := Parent(N);
    K := BaseRing(R);
    q := #K;

    polynomialsLo := PolynomialsUptoDegree(q, Degree(P)*(k-1) - 1);
    polynomialsHi := PolynomialsUptoDegree(q, Degree(P)*k - 1);

    result := [];

    for i := 1 to d+1 do
        maxIndices := [#polynomialsLo : j in [1..i-1]] cat [#polynomialsHi : j in [i+1..d+1]];
        indices := [1 : j in [1..#maxIndices]];
        hasNext := true;
        repeat
            Append(~result, [P*polynomialsLo[indices[j]] : j in [1..i-1]] cat [1] cat [polynomialsHi[indices[j]] : j in [i..d]]);
            IndexListAddOne(~indices, ~hasNext, maxIndices);
        until not hasNext;
    end for;

    return result;
end function;

intrinsic ProjectiveSpaceRepresentants(d::RngIntElt, factorPolynomials::SeqEnum) -> SeqEnum
{ Returns a set of representants of the projective space mod N of dimension d }
    R := Universe(factorPolynomials);
    K := BaseRing(R);

    require IsField(K) and IsFinite(K) : "Base ring needs to be finite field";

    if #factorPolynomials eq 1 then
        return ProjectivePrimarySpace(d, factorPolynomials[1]);
    end if;

    proj := [ProjectivePrimarySpace(d, factorPolynomials[i]) : i in [1..#factorPolynomials]];
    result := [];

    maxIndices := [#proj[i] : i in [1..#factorPolynomials]];
    indices := [1 : i in [1..#factorPolynomials]];
    hasNext := true;
    repeat
        v := [proj[i][indices[i]] : i in [1..#factorPolynomials]];

        lift := [CRT([v[j][i] : j in [1..#factorPolynomials]], factorPolynomials) : i in [1..d+1]];
        Append(~result, lift);

        IndexListAddOne(~indices, ~hasNext, maxIndices);
    until not hasNext;

    return result;  
end intrinsic;

// g^-1 mod N
function modularInverse(g, N)
    _, s, _ := Xgcd(g, N);
    return s;
end function;

// GCD(s, t^\infty)
function fullPrimesDivisor(s, t)
    erg := Gcd(s, t);
    d := erg;
    r := s;
    for i := 1 to Degree(s) do
        if d eq 1 then
            break i;
        end if;
        r := r div d;
        d := Gcd(r, d^(2^(i - 1)));
        erg := erg * d;
    end for;
    return erg;
end function;

function ProjectivePrimaryReduce(v, prime)
    // assume prime is a power of a prime

    // find minimal j0, such that GCD(v_0, ..., v_j0) = 1
    j0 := -1;
    for j := 1 to #v do
        if GCD([v[i] : i in [1..j]] cat [prime]) eq 1 then
            j0 := j;
            break;
        end if;
    end for;

    // normalize at j0
    primeComponent := fullPrimesDivisor(v[j0], prime);
    unitComponent := v[j0] div primeComponent;
    u := modularInverse(unitComponent, prime);
    return [u*v[i] mod prime : i in [1..#v]];
end function;

intrinsic ProjectiveReduce(v::SeqEnum, factor::SeqEnum) -> SeqEnum
{ Given v, return its canonical representant in the projective space mod N.
  N is given as its factorization, that is a list of polynomials which are powers of primes }

    N := &*factor;
    R := Universe(v);

    if #factor eq 1 then
        return ProjectivePrimaryReduce([x mod factor[1] : x in v], factor[1]);
    end if;

    // reduce in each component
    vComponents := [[R| v[j] mod factor[i]: j in [1..#v]] : i in [1..#factor]];
    vComponents := [ProjectivePrimaryReduce(vComponents[i], factor[i]) : i in [1..#factor]];

    return [CRT([vComponents[j][i] : j in [1..#factor]], factor) : i in [1..#v]];
end intrinsic;

intrinsic ProjectiveEquivalent(u::SeqEnum, v::SeqEnum, N::RngUPolElt) -> Bool
{ Check if two elements u, v are equivalent in the projective space mod N }
    for i := 1 to #u do
        for j := 1 to i-1 do
            if (u[i]*v[j] mod N) ne (u[j]*v[i] mod N) then
                return false;
            end if;
        end for;
    end for;
    return true;
end intrinsic;

intrinsic ProjectiveProductRepresentants(d::RngIntElt, factorPolynomials::SeqEnum) -> SeqEnum
{ Returns a set of representatives of the product P^1 x ... x P^d }
    R := Universe(factorPolynomials);
    K := BaseRing(R);
    q := #K;

    projectives := [ProjectiveSpaceRepresentants(i, factorPolynomials) : i in [1..d]];

    result := [];

    maxIndices := [#projectives[i] : i in [1..d]];
    indices := [1 : i in [1..d]];
    hasNext := true;
    repeat
        v := Reverse([projectives[i][indices[i]] : i in [1..d]]);
        Append(~result, v);
        IndexListAddOne(~indices, ~hasNext, maxIndices);
    until not hasNext;

    return result;
end intrinsic;

intrinsic PrimaryProjectiveToFlag(repr::SeqEnum, N::RngUPolElt) -> SeqEnum
{ Given an element of P^d x ... x P^1, over A/N where N=p^r is primary,
  construct the corresponding flag in (A/N)^d+1 }
    R := Parent(N);
    K := BaseRing(R);
    q := #K;
    d := #repr;

    flag := [repr[1]];

    basis := [1..d+1];

    for i := 1 to d do
        v := repr[i];
        j := [ k : k in [1..#v] | GCD(v[k], N) eq 1 ][1];
        Remove(~basis, j);

        if i lt d then
            w := repr[i+1];
        else
            w := [R|1];
        end if;

        W := [R| 0 : k in [1..d+1]];
        for j in [1..#basis] do
            W[basis[j]] := w[j];
        end for;
        Append(~flag, W);
    end for;

    return flag;
end intrinsic;

intrinsic ProjectiveToFlag(repr::SeqEnum, factorPolynomials::SeqEnum) -> SeqEnum
{ Given an element of P^d x ... x P^1, over A/N, where N is given as factorization f_1 * .. * f_r where the f_i are primary and pair-wise co-prime
  construct the corresponding flag in (A/N)^d+1 }
    components := [PrimaryProjectiveToFlag(repr, Q) : Q in factorPolynomials];

    if #components eq 1 then
        return components[1];
    else
        return 
            [
                [ CRT([components[j][k][i] : j in [1..#factorPolynomials]], factorPolynomials) 
                    : i in [1..#components[1][k]] ]
                : k in [1..#components[1]]
            ];
    end if;
end intrinsic;

intrinsic ProjectiveToMatrix(repr::SeqEnum, factorPolynomials::SeqEnum) -> Mtrx
{ Given an element of P^d x ... x P^1, construct a corresponding flag and return a corresponding matrix in Gamma0 }
    R := Universe(repr[1]);
    flag := ProjectiveToFlag(repr, factorPolynomials);

    // construct matrix from flag as rows from bottom to top
    M := Matrix(R, Reverse(flag));

    // columns from left to right
    //M := Transpose(Matrix(R, flag));

    N := &*factorPolynomials;

    
    if Determinant(M) ne 1 then
        if Determinant(M) mod N ne 1 then
            _,u,_ := Xgcd(Determinant(M), N);
            for i := 1 to NumberOfColumns(M) do
                M[1,i] := u*M[1,i] mod N;
            end for;
        end if;
        M := LiftSLMod(M, N);
    end if;

    return ReverseColumns(M);
end intrinsic;

intrinsic PrimaryFlagToProjective(flag::SeqEnum, N::RngUPolElt) -> SeqEnum
{ Given a flag in A/N^d+1 where N=p^k is primary, return the corresponding flag in P^d x ... x P^1 }
    R := Universe(flag[1]);
    K := BaseRing(R);
    q := #K;
    d := #flag - 1;

    projective := [ProjectiveReduce(flag[1], [N])];

    basis := [1..d+1];

    for i := 1 to d-1 do
        v := ProjectiveReduce(flag[i], [N]);
        j := [ k : k in [1..#v] | GCD(v[k], N) eq 1 ][1];
        Remove(~basis, j);

        for l := i+1 to #flag do
            flag[l] := [w[k]-w[j]*v[k] mod N where w is flag[l] : k in [1..d+1]];
        end for;
        w := flag[i+1];
        w := [w[k]-w[j]*v[k] mod N : k in [1..d+1]];
        W := [ w[b] : b in basis ];

        assert &or{ x ne 0 : x in W };

        W := ProjectiveReduce(W, [N]);
        Append(~projective, W);
    end for;

    return projective;
end intrinsic;

intrinsic FlagToProjective(flag::SeqEnum, factorPolynomials::SeqEnum) -> SeqEnum
{ Given a flag in A/N^d+1, where N is given as factorization f_1 * .. * f_r where the f_i are primary and pair-wise co-prime
  return the corresponding flag in P^d x ... x P^1 }
    components := [PrimaryFlagToProjective(flag, Q) : Q in factorPolynomials];

    if #components eq 1 then
        return components[1];
    else
        return 
            [
                [ CRT([components[j][k][i] : j in [1..#factorPolynomials]], factorPolynomials) 
                    : i in [1..#components[1][k]] ]
                : k in [1..#components[1]]
            ];        
    end if;
end intrinsic;

intrinsic MatrixToProjective(M::Mtrx, factorPolynomials::SeqEnum) -> SeqEnum
{ Given M in Gamma0 and a factorization of N, reconstruct the corresponding flag in P^d x ... x P^1 }
    //flag := [ ElementToSequence(ColumnSubmatrix(M, i, 1)) : i in [1..NumberOfColumns(M)] ];
    M := ReverseColumns(M);
    flag := Reverse([ ElementToSequence(RowSubmatrix(M, i, 1)) : i in [1..NumberOfRows(M)] ]);
    return FlagToProjective(flag, factorPolynomials);
end intrinsic;
