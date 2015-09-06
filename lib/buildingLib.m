/*
 * Copyright (c) 2015 Lutz Hofmann
 * Licensed under the MIT license, see LICENSE.txt for details.
 */

freeze;
declare verbose buildingLib, 1;
LAURENT_EPS := 20;

intrinsic StringReplace(s::MonStgElt, search::MonStgElt, replace::MonStgElt) -> MonStgElt
{}
    result := "";
    while Index(s, search) gt 0 do
        i := Index(s, search);
        result *:= Substring(s, 1, i - 1) * replace;
        s := Substring(s, i + #search, #s);
    end while;
    result *:= s;
    return result;
end intrinsic;

// return a sequence of all polynomials in F_q upto degree
function PolynomialsUptoDegree(q, degree)
    K := GF(q);
    R<T> := PolynomialRing(K);
    result := [R| 0 ];

    for d := 0 to degree do
        result cat:= [R| scalar*T^d + p : scalar in Set(K), p in result | scalar ne 0 ];
    end for;

    return result;
end function;

procedure IndexListAddOne(~list, ~hasNext, maxIndices)
    i := 1;
    carry := false;
    repeat
        if i gt #list then
            hasNext := false;
            return;
        end if;
        
        if list[i] eq maxIndices[i] then
            list[i] := 1;
        else
            list[i] := list[i] + 1;
        end if;

        carry := list[i] eq 1;

        i +:= 1;
    until not carry;
    hasNext := true; 
end procedure;

procedure FiniteFldListAddOne(~list, ~hasNext : StoreCarry := false)
    K := Universe(list);
    if not IsPrimeField(K) then
        elements := Sort(SetToSequence(Set(K)));
    end if;
    i := 1;
    carry := false;
    repeat
        if i gt #list then
            if StoreCarry then
                Append(~list, 1);
            end if;
            hasNext := false;
            return;
        end if;
        
        if IsPrimeField(K) then            
            list[i] +:= 1;
        else
            index := Index(elements, list[i]);
            if index eq #elements then
                list[i] := 0;
            else
                list[i] := elements[index+1];
            end if;
        end if;
        carry := list[i] eq 0;

        i +:= 1;
    until not carry;
    hasNext := true; 
end procedure;

procedure FiniteFldPolynomialListAddOne(~list, ~hasNext, maxDegrees)
    i := 1;
    carry := false;
    repeat
        if i gt #list then
            hasNext := false;
            return;
        end if;
        
        coeffs := Coefficients(list[i]);
        ignore := true;
        FiniteFldListAddOne(~coeffs, ~ignore : StoreCarry := true);
        list[i] := Polynomial(coeffs);

        carry := false;
        if Degree(list[i]) gt maxDegrees[i] then
            list[i] := 0;
            carry := true;
        end if;

        i +:= 1;
    until not carry;
    hasNext := true; 
end procedure;

intrinsic IsGamma0NElement(g::Mtrx, N::RngUPolElt) -> BoolElt
{ Check if a Matrix g is upper triangular modulo N }
    for i := 1 to NumberOfRows(g) do
        for j := 1 to i-1 do
            if g[i,j] mod N ne 0 then
                return false;
            end if;
        end for;
    end for;
    return true;
end intrinsic;

intrinsic StandardVertex(d::RngIntElt) -> Tup
{
    Return the standard d-Vertex
}
    return <0 : i in [1..d]>;
end intrinsic;

intrinsic StandardSimplex(d::RngIntElt) -> SetEnum
{
    Return the standard d-Simplex
}
    return { < j le i select 0 else 1 : j in [1..d] > : i in [0..d]};
end intrinsic;

intrinsic StandardPointedSimplex (d::RngIntElt) -> SeqEnum
{}
    return Sort(SetToSequence(StandardSimplex(d)));
end intrinsic;

intrinsic QuotientRightCosets(quotient::Rec, cosets::SeqEnum, cosetPointer::SeqEnum, group::.) -> SeqEnum, SeqEnum
{}
    groupIsIterator := Type(group) eq Rec;

    if #cosets eq 0 then
        // take trivial cosets
        cosets := [[i] : i in [1..#quotient`representatives]];
        cosetPointer := [1..#quotient`representatives];
    end if;

    resultCosets := [];
    resultPointer := [ 0 : i in [1..#quotient`representatives]];


    if IsVerbose("buildingLib") then
        timeLast := Cputime();
        timeStart := timeLast;
    end if;

    for i := 1 to #cosets do
        if #cosets[i] eq 0 then
            continue;
        end if;
        if IsVerbose("buildingLib") and Cputime(timeLast) gt 10 then
            vprintf buildingLib: "%o/%o (%o) (%o)\n", i, #cosets, Cputime(timeLast), Cputime(timeStart)/i*#cosets;
            timeLast := Cputime();
        end if;

        CurrentElt := quotient`representatives[cosets[i][1]];
        currentCoset := cosets[i];

        if groupIsIterator then
            // make copy of iterator (this is important)
            iterator := group;
            gamma := iterator`currentMatrix;
        else
            k := 1;
        end if;
        while (groupIsIterator and iterator`hasNext) or (not groupIsIterator and k le #group) do
            if groupIsIterator then
                iterator`next(~iterator, ~gamma);
            else
                gamma := group[k];
                k +:= 1;
            end if;

            j := quotient`reductionFunc(quotient, CurrentElt*gamma);
            j := cosetPointer[j];
            if (j ne i) and (#cosets[j] gt 0) then
                currentCoset cat:= cosets[j];
                cosets[j] := [];
            end if;
        end while;

        Append(~resultCosets, currentCoset);
        currentCosetIndex := #resultCosets;
        for repIndex in currentCoset do
            resultPointer[repIndex] := currentCosetIndex;
        end for;
    end for;

    return resultCosets, resultPointer;
end intrinsic;

intrinsic CongruenceSubgroupDoubleCosets(SubGroupCondition::UserProgram, representatives::., cosets::SeqEnum, group::., operation::MonStgElt : fullCosets := true) -> SeqEnum
{
    Given a quotient of Gamma0 by a congruence subgroup, compute its (double) cosets by a finite subgroup.

    The congruence subgroup is given by SubGroupCondition; a function that returns true if a given matrix is contained in the subgroup.

    The initial quotient is given by the parameter cosets. It is a sequence of sequences of integer indices refering to representatives.
    Each element of cosets corresponds to a list of equivalent elements in representatives.
    If the elements in representatives already are mutually in-equivalent, cosets should be the sequence [[i] : i in [1..#representatives]] ("trivial cosets").
    If an empty sequence is passed, default to the "trivial cosets".

    representatives can also be a finite matrix group. Then the indices in cosets refer to the preimages of the group's NumberingMap.
    !Beware that NumberingMap depends on the random seed!

    The group operation used to compute the cosets is given by parameters group and operation.
    operation can either be "left" or "right" and specifies if left respectively right cosets should be computed.
    group can either be a sequence of matrices or a iterator.

    If the optional parameter fullCosets (default: true) is set to false, only a sequence of one representative per coset is returend.

    The returned cosets will be given as indices refering to representatives.

    Examples:
      * representatives := system of representatives of H \ Gamma0, cosets define H \ Gamma0 / G, 
        group := F, operation := "right", we compute (H \ Gamma0 / G) / F
        this is useful when G < F
      * representatives := system of representatives of H \ Gamma0, cosets := [] (or trivial cosets), G := group, operation := "right"
        we compute H \ Gamma0 / G
      * representatives := SpecialLinearGroup(F_q), group := [IdentityMatrix], operation := "left", H := the group given by SubGroupCondition
        if H has a full system of representatives that is contained in SL(F_q), then this will compute H \ Gamma0 (by computing {e] \ (G \ Gamma0))
        Notes: it is adviced to set fullCosets to false for more performance
               representatives can also be SetToSequence(Set(SpecialLinearGroup)) for better performance but more memory usage
}

    require (Type(representatives) eq SeqEnum) or (Type(representatives) eq GrpMat) : "Parameter representatives must be sequence or matrix group.";

    representativesAreGroup := Type(representatives) eq GrpMat;
    if representativesAreGroup then
        require IsFinite(representatives) : "Parameter representatives must be finite group.";
        representativesMap := NumberingMap(representatives);
    end if;

    representativesOrder := representativesAreGroup select Order(representatives) else #representatives;

    require (Type(group) eq SeqEnum) or (Type(group) eq Rec) : "Parameter group must be sequence or iterator.";

    groupIsIterator := Type(group) eq Rec;
    if groupIsIterator then
        require ("next" in Names(group)) and ("hasNext" in Names(group)) and ("currentMatrix" in Names(group)) : "Iterator does not have all required properties.";
    end if;

    require (operation eq "left") or (operation eq "right") : "Parameter operation must be one of left or right.";
    operationIsLeft := operation eq "left";

    if #cosets eq 0 then
        // take trivial cosets
        cosets := [[i] : i in [1..representativesOrder]];
    end if;

    order := #cosets;

    // in the follwing we go through all cosets and check if they are equivalent to any other coset
    // if we find equivalent ones, we join them and set the right-most one to an empty list
    // empty lists do not need to be checked again, thus progressively eliminating possible candidates

    if IsVerbose("buildingLib") then
        timeLast := Cputime();
    end if;
    // iterative divide-and-conquer
    for power := 0 to Floor(Log(2, order-1)) do
        if IsVerbose("buildingLib") then
            vprintf buildingLib: "Level %o/%o (%o)\n", power, Floor(Log(2, order-1)), Cputime(timeLast);
            timeLast := Cputime();
        end if;        

        unit := 2^power;
        for i := 1 to order by unit*2 do
            if i+unit-1 lt order then
                // left: i ... i+unit-1
                // right: i+unit ... Minimum(i+unit*2-1, order)
                // total: i..i+unit*2-1
                for left := i to i+unit-1 do
                    if #cosets[left] eq 0 then
                        continue;
                    end if;

                    if representativesAreGroup then
                        CurrentElt := cosets[left][1] @@ representativesMap;
                    else
                        CurrentElt := representatives[cosets[left][1]];
                    end if;
                    CurrentInv := CurrentElt ^ -1;

                    for right := i+unit to Minimum(i+unit*2-1, order) do
                        if #cosets[right] eq 0 then
                            continue;
                        end if;

                        if representativesAreGroup then
                            OtherElt := cosets[right][1] @@ representativesMap;
                        else
                            OtherElt := representatives[cosets[right][1]];
                        end if;                  

                        if groupIsIterator then
                            // make copy of iterator (this is important)
                            iterator := group;
                            gamma := iterator`currentMatrix;
                        else
                            k := 1;
                        end if;
                        while (groupIsIterator and iterator`hasNext) or (not groupIsIterator and k le #group) do
                            if groupIsIterator then
                                iterator`next(~iterator, ~gamma);
                            else
                                gamma := group[k];
                                k +:= 1;
                            end if;

                            if (operationIsLeft     and SubGroupCondition(OtherElt * gamma * CurrentInv)) or
                               (not operationIsLeft and SubGroupCondition(CurrentInv * gamma * OtherElt)) 
                            then
                                // join the two cosets in to the left-most one
                                if fullCosets then
                                    Insert(~cosets[left], #cosets[left] + 1, #cosets[left], cosets[right]);
                                end if;
                                // clear right-most coset
                                cosets[right] := [];
                                break;
                            end if;
                        end while;
                    end for;
                end for;
            end if;
        end for;
    end for;

    if not fullCosets then
        return [ coset[1] : coset in cosets | #coset gt 0 ];
    else
        return [ coset : coset in cosets | #coset gt 0 ];
    end if;
end intrinsic;

function AllFiniteFldLists(list)
    result := [];
    hasNext := true;
    repeat
        Append(~result, list);
        FiniteFldListAddOne(~list, ~hasNext);
    until not hasNext;      
    return result;
end function;

function SL3_ALGORITHM_MAKE_COEFF_LISTS()
    list := AllFiniteFldLists([GF(2)| 0 : i in [1..6]]);
    list := [[Integers()| i : i in l] : l in list];
    Sort(~list, func<a,b| #[i : i in[1..6] | a[i] ne 0] - #[i : i in[1..6] | b[i] ne 0]>);
    return list;
end function;

SL3_ALGORITHM_COEFF_LIST := SL3_ALGORITHM_MAKE_COEFF_LISTS();

// guess a lift in SL_3(A) of a matrix in SL_3(A/N)
function SL3LiftMatrixMod(matrix, N)
    R := BaseRing(matrix);

    d, e, f := Explode(ElementToSequence(matrix[2]));
    g, h, i := Explode(ElementToSequence(matrix[3]));

    for shift in SL3_ALGORITHM_COEFF_LIST do
        d1 := d + shift[1] * N;
        e1 := e + shift[2] * N;
        f1 := f + shift[3] * N;
        g1 := g + shift[4] * N;
        h1 := h + shift[5] * N;
        i1 := i + shift[6] * N;

        gcd := GCD([ e1*i1 - h1*f1, g1*f1 - d1*i1, d1*h1 - g1*e1  ]);
        if gcd eq 1 then
            _, bezout := XGCD([ e1*i1 - h1*f1, g1*f1 - d1*i1, d1*h1 - g1*e1 ]);
            a, b, c := Explode(ElementToSequence(matrix[1]));

            res := Determinant(matrix) div N;
            res +:= a*e*(i1 div N) + a*(e1 div N)*i1;
            res +:= c*h*(d1 div N) + c*(h1 div N)*d1;
            res +:= b*f*(g1 div N) + b*(f1 div N)*g1;
            res -:= c*e*(g1 div N) + c*(e1 div N)*g1;
            res -:= a*h*(f1 div N) + a*(h1 div N)*f1;
            res -:= b*d*(i1 div N) + b*(d1 div N)*i1;
            a1 := a - res*bezout[1]*N;
            b1 := b - res*bezout[2]*N;
            c1 := c - res*bezout[3]*N;

            matrixLift := Matrix(R, 3, 3, [a1, b1, c1, d1, e1, f1, g1, h1, i1]);        

            return matrixLift;
        end if;
    end for;

    error "Could not lift bottom two rows.";
end function;


intrinsic LiftSLMod(M::Mtrx, N::RngUPolElt : EnableGuess := false) -> Mtrx
{ 
    given a matrix M with det(M) = 1 mod N, return a matrix M' with det(M') = 1 and M' = M mod N. 

    if optional parameter EnableGuess is set to true, will attempt to guess a lift in the d=2 case.
}
    require NumberOfRows(M) eq NumberOfColumns(M) : "M needs to be square matrix.";
    R := Parent(N);
    K := BaseRing(R);
    require IsField(K) and IsFinite(K) : "Need to have underlying finite field.";
    require BaseRing(Parent(M)) eq Parent(N) : "Polynomial rings must match.";

    assert2 Determinant(M) mod N eq 1;

    n := NumberOfRows(M);

    if EnableGuess and (n eq 3) then
        // try to guess a lift
        try
            lift := SL3LiftMatrixMod(M, N);
            return lift;
        catch e
            lift := 0;
        end try;
    end if;

    if n eq 1 then
        assert M[1,1] mod N eq 1;
        return Matrix(R, 1, 1, [R!1]);
    end if;

    S, U, V := SmithForm(M);   

    if Determinant(U) ne 1 then
        det := Determinant(U);
        A := IdentityMatrix(R,n);
        A[1,1] := det;
        U := A^-1 * U;
        S := A^-1 * S;
    end if;
    if Determinant(V) ne 1 then
        det := Determinant(V);
        A := IdentityMatrix(R,n);
        A[1,1] := det;
        V := V * A^-1;
        S := S * A^-1;
    end if;    

    assert2 Determinant(U) eq 1;
    assert2 Determinant(V) eq 1;    
    assert2 U*M*V eq S;
    assert2 &*[ S[i,i] : i in [1..n] ] mod N eq 1;
    assert2 &*[ S[i,i] : i in [1..n] ] eq Determinant(M);

    C := LiftSLMod(DiagonalMatrix(R, [S[1,1]*S[2,2]] cat [S[i,i] : i in [3..n]]), N);
    assert2 Determinant(C) eq 1;

    b := &*[ S[i,i] : i in [2..n] ];
    W := DiagonalJoin(Matrix(R,2,2,[b,1,b-1,1]), IdentityMatrix(R, n-2));
    X := IdentityMatrix(R, n);
    X[1,2] := -S[2,2];

    A := DiagonalJoin(Matrix(R,1,1,[R!1]), C);
    A[2,1] := 1 - S[1,1];

    assert2 Determinant(U) eq 1;
    assert2 Determinant(V) eq 1;
    assert2 Determinant(W) eq 1;
    assert2 Determinant(X) eq 1;
    assert2 Determinant(A) eq 1;

    return U^-1 * W^-1 * A * X^-1 * V^-1;
end intrinsic;

intrinsic AllMatricesFromTemplate(q::RngIntElt, Template::Mtrx : CheckInvertible := false) -> SeqEnum[Mtrx]
{
    Enumerate all matrices defined by an integer-valued template matrix.
    If CheckInvertible is set to true, only return invertible such matrices.
}
    require NumberOfRows(Template) eq NumberOfColumns(Template) : "Template needs to be square matrix.";
    n := NumberOfRows(Template);
    k := GF(q);
    R<T> := PolynomialRing(k);

    maxDegrees := ElementToSequence(Template);
    // enumerate all needed lists of polynomials
    polynomials := [PolynomialsUptoDegree(q, d) : d in maxDegrees];

    // intialize index-lists counting algorithm
    maxIndices := [#l : l in polynomials];
    indexList := [1 : i in [1..#polynomials]];
    matrixHasNext := true;

    // loop over all possible index-lists
    matrices := [];
    repeat
        matrix := Matrix(R, n, n, [polynomials[i][indexList[i]] : i in [1..#polynomials]]);
        if not CheckInvertible or IsUnit(matrix) then
            Append(~matrices, matrix);
        end if;
        IndexListAddOne(~indexList, ~matrixHasNext, maxIndices);
    until not matrixHasNext;
    return matrices;
end intrinsic;

// TODO clean this up, make iterator for upper triangulars
intrinsic AllMatricesFromTemplate_Iterator(q::RngIntElt, Template::Mtrx : CheckInvertible := false) -> Rec
{...}
    procedure AllMatricesFromTemplate_Next(~Iterator, ~result)
        result := Iterator`currentMatrix;

        if Iterator`currentIsLast then
            Iterator`hasNext := false;
            return;
        end if;

        hasNext := true;
        M := ElementToSequence(Iterator`currentMatrix);
        while hasNext do
            FiniteFldPolynomialListAddOne(~M, ~hasNext, Iterator`maxDegrees);
            matrix := Matrix(Iterator`baseRing, Iterator`dimension, Iterator`dimension, M);
            if not Iterator`checkInvertible or IsUnit(matrix) then
                Iterator`currentMatrix := matrix;
                Iterator`hasNext := true;
                Iterator`currentIsLast := not hasNext;
                return;
            end if;
        end while;

        Iterator`hasNext := false;
    end procedure;

    n := NumberOfRows(Template);
    k := GF(q);
    R<T> := PolynomialRing(k);
    maxDegrees := ElementToSequence(Template);
    M := [R| 0 : i in maxDegrees];

    matrixHasNext := true;
    foundMatrix := false;
    repeat
        matrix := Matrix(R, n, n, M);
        if not CheckInvertible or IsUnit(matrix) then
            foundMatrix := true;
            break;
        end if;
        FiniteFldPolynomialListAddOne(~M, ~matrixHasNext, maxDegrees);
    until not matrixHasNext;

    AllMatricesFromTemplate_Iter := recformat < 
        maxDegrees : SeqEnum,
        dimension : RngIntElt,
        baseRing : RngUPol,
        checkInvertible : BoolElt,
        currentMatrix : Mtrx,
        hasNext : BoolElt,
        currentIsLast : BoolElt,
        next : UserProgram
    >;    

    iterator := rec< AllMatricesFromTemplate_Iter | 
                        maxDegrees := maxDegrees,
                        dimension := n,
                        baseRing := R,
                        checkInvertible := CheckInvertible,
                        currentMatrix := matrix,
                        hasNext := foundMatrix,
                        currentIsLast := not matrixHasNext,
                        next := AllMatricesFromTemplate_Next >;
    return iterator;
end intrinsic;

intrinsic Gamma0UpperTriagSubgroupFromTemplate(q::RngIntElt, Template::Mtrx) -> SeqEnum[Mtrx]
{
    Same as AllMatricesFromTemplate, but for upper triangular templates; only returns invertible such matrices.
    All entries on the lower triangle will be ignored and it is assumed there are only zeros on the diagonal.

    Faster than AllMatricesFromTemplate as there is an obvious optimization for only enumerating invertible matrices.
}
    require NumberOfRows(Template) eq NumberOfColumns(Template) : "Template needs to be square matrix.";
    n := NumberOfRows(Template);
    k := GF(q);
    R<T> := PolynomialRing(k);

    // enumerate all matrices defined by template with zeros on diagonal
    upperTemplate := [i le j-1 select Template[i,j] else -1 : j in [1..n], i in [1..n]];
    upperTriags := AllMatricesFromTemplate(q, Matrix(n,n,upperTemplate) : CheckInvertible := false );

    subgroup := [];

    diagonalHasNext := true;

    // iterate over all possible diagonals that make the matrix invertible (<-> doesn't have zeros)
    scalars := SetToSequence(Set(k) diff {k| 0});
    diagonalMaxIndices := [#scalars : i in [1..n]];
    diagonalIndex := [1 : i in [1..n]];
    repeat
        diagonal := [scalars[diagonalIndex[i]] : i in [1..n]];        
        diagonalMatrix := DiagonalMatrix(R, diagonal);

        subgroup cat:= [ diagonalMatrix + upper : upper in upperTriags ];

        IndexListAddOne(~diagonalIndex, ~diagonalHasNext, diagonalMaxIndices);
    until not diagonalHasNext;

    return subgroup;
end intrinsic;

intrinsic Gamma0SimplexFixgroupTemplateReduce(template::AlgMatElt[RngInt], modulus::RngIntElt) -> AlgMatElt[RngInt]
{
    Reduces the entries of the template by modulus.
    modlus should usually be deg(N) if the congruence subgroup is given by congruences mod N.
    Also normalizes all negative entries to -1.
}

    for i := 1 to NumberOfRows(template) do
        for j := 1 to NumberOfColumns(template) do
            if template[i,j] gt 0 then
                template[i,j] := Minimum(template[i,j], modulus-1);
            end if;
            if template[i,j] lt 0 then
                template[i,j] := -1;
            end if;
        end for;
    end for;
    return template;
end intrinsic;

intrinsic Gamma0SimplexFixgroupTemplate(simplex::SeqEnum[Tup]) -> AlgMatElt[RngInt]
{
    Given a simplex in the Weyl Chamber as a sequence of vertices, return a template of its Gamma0-fixgroup.
    The Gamma0-fixgroup is then given by the subgroup of Gamma0 where each entry has
    polynomial degree smaller or equal than in the template.
}

    require &and[ #simplex[i] eq #simplex[i+1] : i in [1..#simplex-1] ] : "Coordinates need to be of same length";
    require #simplex gt 0 : "Need at least one coordinate";

    d := #simplex[1];
    Template := Matrix(Integers(), d+1, d+1, [0 : i in [1..(d+1)*(d+1)]]);

    // add 0 coordinate
    nodes := [Insert(TupleToList(node),1,0) : node in simplex];

    for i := 1 to d+1 do
        for j := 1 to d+1 do
            Template[i,j] := Minimum([ node[j]-node[i] : node in nodes ]);
        end for;
    end for;

    return Template;
end intrinsic;

intrinsic Gamma0SubgroupEqual(TemplateL::AlgMatElt[RngInt], TemplateR::AlgMatElt[RngInt]) -> BoolElt
{
    Given two Gamma0-subgroup templates, checks if the two subgroups are equal
}

    return &and[ (x[i] lt 0 and y[i] lt 0) or (x[i] eq y[i])
                 where x is ElementToSequence(TemplateL)
                 where y is ElementToSequence(TemplateR)
                 : i in [1..#ElementToSequence(TemplateL)] ];
end intrinsic;

intrinsic Gamma0SubgroupIsContained(TemplateL::AlgMatElt[RngInt], TemplateR::AlgMatElt[RngInt]) -> BoolElt
{
    Given two Gamma0-subgroup templates, checks if the left subgroup is contained in the right one
}
    return &and[ (x[i] lt 0 and y[i] lt 0) or (x[i] le y[i])
                 where x is ElementToSequence(TemplateL)
                 where y is ElementToSequence(TemplateR)
                 : i in [1..#ElementToSequence(TemplateL)] ];
end intrinsic;

intrinsic Gamma0SubgroupFromTemplate(q::RngIntElt, Template::AlgMatElt[RngInt]) -> SeqEnum[Mtrx]
{
    Enumerates all elements of a Gamma0-subgroup given by a template.
    Chooses the fast upper-triangular algorithm if possible.
}
    require NumberOfRows(Template) eq NumberOfColumns(Template) : "Template must be square";

    d := NumberOfRows(Template) - 1;

    if &and[ Template[i,j] lt 0 : i in [1..d+1], j in [1..d+1] | i gt j ] then
        return Gamma0UpperTriagSubgroupFromTemplate(q, Template);
    else
        return AllMatricesFromTemplate(q, Template : CheckInvertible := true);
    end if;
end intrinsic;

intrinsic Gamma0SimplexFixgroup(q::RngIntElt, simplex::SeqEnum[Tup]) -> SeqEnum[Mtrx]
{
    Given a simplex, enumerates all element in its Gamma0-fixgroup
}
    require &and[ #simplex[i] eq #simplex[i+1] : i in [1..#simplex-1] ] : "Coordinates need to be of same length";

    Template := Gamma0SimplexFixgroupTemplate(simplex);
    return Gamma0SubgroupFromTemplate(q, Template);
end intrinsic;

function compare(x,y)
    if x lt y then
        return -1;
    elif x eq y then
        return 0;
    else
        return 1;
    end if;
end function;

intrinsic LaurentSeriesSum(x::RngSerLaurElt, n::RngIntElt, m::RngIntElt) -> RngUPolElt, RngSerLaurElt, RngSerLaurElt
{
    For x in F_q((pi)) write x = pi^n * P + y + pi^m * z
        where P in F_q[T],
        n < v(y) < m, deg(y) < m
        0 <= v(z)
    return P,y,z
}

    Kinf := Parent(x);
    K := BaseRing(Kinf);
    PI := UniformizingElement(Kinf);

    coeff, v := Coefficients(x);

    polyEnd := Minimum(#coeff, n - v + 1);
    polyCoeff := [coeff[i] : i in [1..polyEnd]];
    for i in [1..polyEnd] do
        coeff[i] := 0;
    end for;
    P := Polynomial(K, Reverse(polyCoeff cat [0 : i in [#polyCoeff..n-v]]));

    middleStart := Maximum(1, polyEnd + 1);
    middleEnd := Minimum(#coeff, m - v);
    middleCoeff := [coeff[i] : i in [middleStart..middleEnd]];
    for i in [middleStart..middleEnd] do
        coeff[i] := 0;
    end for;    
    middleValuation := v + middleStart - 1;
    if #middleCoeff eq 0 then
        y := Kinf ! 0;
    else
        y := elt<Kinf| middleValuation, middleCoeff, -1>;
    end if;

    lastStart := Maximum(1, Minimum(#coeff, m - v + 1));
    lastEnd := #coeff;
    lastCoeff := [coeff[i] : i in [lastStart..lastEnd]];
    lastValuation := v + lastStart - 1 - m;
    if #lastCoeff eq 0 then
        z := Kinf ! 0;
    else
        z := elt<Kinf| lastValuation, lastCoeff, -1>;
    end if;

    assert2 IsWeaklyEqual(x, PolynomialToLaurent(P,Kinf)*PI^n + y + z*PI^m);
    assert2 IsWeaklyZero(y) or Valuation(y) gt n;
    if n lt m then
        assert2 n lt Valuation(y);
        assert2 IsWeaklyZero(y) or m gt Valuation(y);
        assert2 IsWeaklyZero(y) or Degree(y) lt m;
    end if;
    assert2 0 le Valuation(z);

    return P, y, z;
end intrinsic;

intrinsic LaurentIntegerComponent(x::RngSerLaurElt) -> RngSerLaurElt
{ For a unit x in K_inf return a unit u in O_inf such that
    x = pi^v(x) * u
}
    if IsWeaklyZero(x) then
        return Parent(x) ! 0;
    end if;
    
    Kinf := Parent(x);
    PI := UniformizingElement(Kinf);
    return x * (PI^-Valuation(x));
end intrinsic;

function TruncateMatrix(M)
    Kinf := BaseRing(Parent(M));
    return Matrix(Kinf, NumberOfRows(M), NumberOfColumns(M), [Truncate(x) : x in ElementToSequence(M)]);
end function;

function LaurentEqual(M, N : epsilon := LAURENT_EPS)
    R := BaseRing(Parent(M));
    _, precision := HasAttribute(R, "DefaultPrecision");
    epsilon := precision - epsilon;

    m := NumberOfRows(M);
    n := NumberOfColumns(M);
    if not &and{IsWeaklyZero(M[i,j] - N[i,j]) or Valuation(M[i,j] - N[i,j]) ge epsilon  : i in [1..m], j in [1..n] } then
        print "Assertion failed (eps=", epsilon, "):\n", M, "=/=", N;
        return false;
    end if;
    return true;
end function;

function PowerSeriesRingFromLaurent(Kinf)
/*
    Given a Laurent series ring Kinf, return power series ring of same precision
*/
    K := BaseRing(Kinf);
    _, precision := HasAttribute(Kinf, "DefaultPrecision");
    if not IsFinite(Precision(Kinf)) then
        return PowerSeriesRing(K : Precision := precision);
    else
        // fixed precision
        return PowerSeriesRing(K, precision);
    end if;
end function;


intrinsic Valuation(x::FldFunRatUElt) -> .
{
    Degree Valuation for univariante rational function fields, 
    returns Infinity for x=0, an integer otherwise
    Note that this overloads magma's built-in function Valuation
}

    if x eq 0 then
        return Infinity();
    else
        f := Numerator(x);
        g := Denominator(x);
        return Degree(g) - Degree(f);
    end if;
end intrinsic;

intrinsic RationalIntegerComponent(x::FldFunRatUElt) -> FldFunRatUElt
{ 
    For a unit x in F_q(T) return a unit u in F_q(T) such that
    x = T^-v(x) * u  and v(u) >= 0
}
    if x eq 0 then
        return Parent(x) ! 0;
    end if;
    
    Quot := Parent(x);
    PI := Quot.1^-1;    
    return x * (PI^-Valuation(x));
end intrinsic;


intrinsic BuildingVertexDecomposition(M::Mtrx) -> Mtrx, Mtrx, RngSerLaurElt
{
    Given a Matrix in GL(K_inf), return
        g in GL(K_inf) upper diagonal with only powers of PI on the diagonal,
        h in GL(O_inf),
        alpha a unit of K_inf
    such that
        g = M*h*alpha
}
    require NumberOfRows(M) eq NumberOfColumns(M) : "Matrix needs to be square."; 
    n := NumberOfRows(M);

    Kinf := BaseRing(Parent(M));    
    require Type(Kinf) eq RngSerLaur : "Base ring needs to be Laurent series ring.";
    PI := UniformizingElement(Kinf);
    K := BaseRing(Kinf);
    require IsField(K) and IsFinite(K) : "Need to have underlying finite field.";
    Oinf := PowerSeriesRingFromLaurent(Kinf);
    R := PolynomialRing(K);    

    // start with identity elements
    h := IdentityMatrix(Oinf, n);
    alpha := Kinf ! 1;

    M0 := M;

    for i := n to 2 by -1 do
        // get elements below diagonal in row i
        lowerDiagRow := ElementToSequence(M[i]);
        lowerDiagRow := [lowerDiagRow[j] : j in [1..i]];

        // find entry with smallest valuation
        valuations := [Valuation(x) : x in lowerDiagRow];
        minValuation := Minimum(valuations);
        minValuationIndex := Index(valuations, minValuation);
        minValuationElt := lowerDiagRow[minValuationIndex];

        // swap columns so that entry with smallest valuation is on diagonal
        if minValuationIndex lt i then
            permutation := [1..n];
            permutation[i] := minValuationIndex;
            permutation[minValuationIndex] := i;
            P := PermutationMatrix(Oinf, permutation);
            h := h * P;
            M := M * P;
        end if;

        // eliminate entries left of diagonal
        A := IdentityMatrix(Oinf, n);
        for j := 1 to i-1 do
            A[i,j] := -M[i,j]/minValuationElt;
        end for;
        h := h * A;
        M := M * A;
    end for;

    // change bottom right entry to 1
    alpha := M[n,n]^-1;
    M := M * M[n,n]^-1;

    // divide diagonal by integral units
    A := DiagonalMatrix(Oinf, [LaurentIntegerComponent(M[i,i])^-1 : i in [1..n]]);
    h := h * A;
    M := M * A;

    assert2 &and{IsWeaklyZero(M[i,j]) : i,j in [1..n] | i gt j};
    assert2 LaurentEqual(M, M0*h*alpha);    

    return M, h, alpha;
end intrinsic;

intrinsic PolynomialToLaurent(P::RngUPolElt, Kinf::RngSerLaur) -> RngSerLaurElt
{
        Treat the generator of the Laurent series ring as 1/T
        to cast the polynomial P to the corresponding laurent series.    
}
    return elt<Kinf| -Degree(P), Reverse(Coefficients(P)), -1>;
end intrinsic;

intrinsic PolynomialMatrixToLaurent(M::Mtrx, Kinf::RngSerLaur) -> Mtrx
{
        Uses PolynomialToLaurent on each entry of the matrix.
}
    return Matrix(Kinf, NumberOfRows(M), NumberOfColumns(M), 
                  [PolynomialToLaurent(P, Kinf) : P in ElementToSequence(M)]);
end intrinsic;

intrinsic LaurentToPolynomial(x:RngSerLaurElt) -> RngUPolElt
{}
    K := BaseRing(Parent(x));
    R := PolynomialRing(K);

    if IsWeaklyZero(x) then
        return R ! 0;
    end if;

    require Degree(x) le 0 : "Not a polynomial.";

    return Polynomial(K, Reverse(Coefficients(x) cat [0 : i in [1..-Degree(x)]]));
end intrinsic;

intrinsic LaurentMatrixIsPolynomial(M::Mtrx) -> BoolElt
{}
    return &and[ IsWeaklyZero(x) or (Degree(x) le 0) : x in ElementToSequence(M) ];
end intrinsic;

intrinsic LaurentMatrixToPolynomial(M::Mtrx) -> Mtrx
{}
    K := BaseRing(BaseRing(Parent(M)));
    R := PolynomialRing(K);
    return Matrix(R, NumberOfRows(M), NumberOfColumns(M), [LaurentToPolynomial(x) : x in ElementToSequence(M)]);
end intrinsic;

intrinsic WeylChamberVertexDecomposition(M::Mtrx) -> Mtrx, Tup, Mtrx, RngSerLaurElt
{
    Given a Matrix in GL(K_inf), return 
        g in GL(F_q[T]), 
        a vertex v in the weyl chamber in homogenous coordinate tuple,
        h in GL(O_inf),
        alpha a unit of K_inf
    such that
        g * M * h * alpha = [v]
    where [v] is the canonical representative of v as a matrix in GL(K_inf)

    i.e. the following should hold:
        PolynomialMatrixToLaurent(g, Kinf) * M * h * alpha eq WeylChamberCoordinatesToMatrix(v, Kinf)
    Note that due to rounding errors, this equality only holds up to o(PI)-terms
}

    require NumberOfRows(M) eq NumberOfColumns(M) : "Matrix needs to be square.";
    n := NumberOfRows(M);

    Kinf := BaseRing(Parent(M));
    require Type(Kinf) eq RngSerLaur : "Base ring needs to be Laurent series ring.";
    K := BaseRing(Kinf);
    require IsField(K) and IsFinite(K) : "Need to have underlying finite field.";

    M0 := M;

    procedure ReduceUpperTriagEntry(~M, i, j, ~g, ~h, Kinf, Oinf, R, n)
    /*
        Reduce i,jth entry of M mod PI where i < j.
        if  n is the valuation of the diagonal entry i,i
        and m is the valuation of the diagonal entry j,j
        then the entry a := M[i,j] will be reduced to
            n < v(a), deg(a) < m
    */
        // write M[i,j] = pi^n * P + y + pi^m * z
        P, y, z := LaurentSeriesSum(M[i,j], Valuation(M[j,j]), Valuation(M[i,i]));

        // eliminiate z summand of M[i,j]
        A := IdentityMatrix(Oinf, n);
        A[i,j] := -z;
        h := h * A;
        M := M * A;

        // eliminate P summand of M[i,j]
        A := IdentityMatrix(R, n);
        A[i,j] := -P;
        g := A * g;
        M := PolynomialMatrixToLaurent(A, Kinf) * M;
    end procedure;

    procedure ReduceDiagonalEntry(~M, i, ~g, ~h, ~alpha, Kinf, Oinf, R, n)
    /*
        Reduces the valuation of the i,i th diagonal entry.
        Might also reduce valuations of the diagonal entreis further below.
        Will keep zero entries in the upper diagonal area below i,
        diagonal entries will be normalized to be only powers of PI.
    */
        PI := UniformizingElement(Kinf);

        // find entry with smallest valuation
        upperDiagRow := ElementToSequence(M[i]);
        upperDiagRow := [upperDiagRow[j] : j in [i+1..n]];        
        valuations := [Valuation(x) : x in upperDiagRow];
        minValuation := Minimum(valuations);
        minValuationIndex := Index(valuations, minValuation);
        minValuationElt := upperDiagRow[minValuationIndex];
        // transform index to matrix coordinates
        minValuationIndex +:= i;

        if IsWeaklyZero(minValuationElt) then
            return;
        end if;

        // eliminate diagonal entry
        A := IdentityMatrix(Oinf, n);
        A[minValuationIndex, i] := -PI^Valuation(M[i,i]) * minValuationElt^-1;
        h := h * A;
        M := M * A;

        // eliminate all other entries on row i
        for j := i+1 to n do
            if j ne minValuationIndex then
                A := IdentityMatrix(Oinf, n);
                A[minValuationIndex, j] := -M[i,j] * minValuationElt^-1;
                h := h * A;
                M := M * A;                
            end if;
        end for;

        // swap rows
        permutation := [1..n];
        permutation[i] := minValuationIndex;
        permutation[minValuationIndex] := i;
        A := PermutationMatrix(R, permutation);
        g := A * g;
        M := PolynomialMatrixToLaurent(A, Kinf) * M;        

        // divide diagonal by integral units
        A := DiagonalMatrix(Oinf, [LaurentIntegerComponent(M[j,j])^-1 : j in [1..n]]);
        h := h * A;
        M := M * A;       
    end procedure;


    PI := UniformizingElement(Kinf);
    Oinf := PowerSeriesRingFromLaurent(Kinf);
    R := PolynomialRing(K);

    g := IdentityMatrix(R, n);

    M, h, alpha := BuildingVertexDecomposition(M);
    assert2 LaurentEqual(M, M0*h*alpha);
    assert2 &and{IsWeaklyZero(N[i,j]) where N is PolynomialMatrixToLaurent(g, Kinf) * M0 * h * alpha : i,j in [1..n] | i gt j};

    for i := n-1 to 1 by -1 do
        // reduce elements right to diagonal "mod diagonal entries"
        for j := n to i+1 by -1 do
            ReduceUpperTriagEntry(~M, i, j, ~g, ~h, Kinf, Oinf, R, n);
        end for;        

        while not &and{IsWeaklyZero(M[i,j]) : j in [i+1..n]} do
            // reduce valuation of diagonal entry
            ReduceDiagonalEntry(~M, i, ~g, ~h, ~alpha, Kinf, Oinf, R, n);

            // reduce elements right to diagonal "mod diagonal entries"
            for j := n to i+1 by -1 do
                ReduceUpperTriagEntry(~M, i, j, ~g, ~h, Kinf, Oinf, R, n);                
            end for;
        end while;

        assert2 LaurentEqual(PolynomialMatrixToLaurent(g, Kinf) * M0 * h * alpha, M);
    end for;    

    assert2 &and{IsWeaklyZero(M[i,j]) : i,j in [1..n] | i ne j};

    // get normalized coordinates of vertex
    
    coord := [Valuation(M[i,i]) : i in [1..n]];
    minValuation := Minimum(coord);
    
    // divide by smallest valuation <=> multiplication with an element of Z(K_inf)
    coord := [coord[i] - minValuation : i in [1..n]];
    alpha *:= PI^(-minValuation);
    M *:= PI^(-minValuation);

    // sort diagonal <=> left and right multiplication with a permutation matrix
    coord, permutation := Sort(coord, func<x,y| x-y>);
    coord := <coord[i] : i in [2..n]>; // coord[1] will always be 1

    A := PermutationMatrix(R, permutation);
    g := A * g;
    h := h * ChangeRing(Transpose(PolynomialMatrixToLaurent(A, Kinf)), Oinf);
    M := PolynomialMatrixToLaurent(A, Kinf) * M * ChangeRing(Transpose(PolynomialMatrixToLaurent(A, Kinf)), Oinf);

    assert2 LaurentEqual(M, WeylChamberCoordinatesToMatrix(coord, Kinf));
    assert2 LaurentEqual(PolynomialMatrixToLaurent(g, Kinf) * M0 * h * alpha, M);
    assert2 LaurentEqual(PolynomialMatrixToLaurent(g, Kinf) * M0 * h * alpha, WeylChamberCoordinatesToMatrix(coord, Kinf));

    assert2 Type(BaseRing(Parent(h))) eq RngSerPow;
    assert2 Type(BaseRing(Parent(g))) eq RngUPol;

    return g, coord, h, alpha;
end intrinsic;

intrinsic WeylChamberMatrixToSimplex(M::Mtrx) -> SeqEnum[Tup]
{}
    require NumberOfRows(M) eq NumberOfColumns(M) : "Matrix needs to be square.";
    n := NumberOfRows(M);

    Kinf := BaseRing(Parent(M));
    require Type(Kinf) eq RngSerLaur : "Base ring needs to be Laurent series ring.";
    K := BaseRing(Kinf);
    require IsField(K) and IsFinite(K) : "Need to have underlying finite field.";

    // compute image of M . standard simplex

    simplex := StandardPointedSimplex(n-1);
    simplex := [M*WeylChamberCoordinatesToMatrix(s, Kinf) : s in simplex];

    return [v where _,v is WeylChamberVertexDecomposition(g) : g in simplex];
end intrinsic;

intrinsic WeylChamberSimplexDecomposition(M::Mtrx) -> Mtrx, SeqEnum[Tup], Mtrx, RngSerLaurElt
{
    Given a Matrix in GL(K_inf), return 
        g in GL(F_q[T]), 
        a pointed simplex s in the weyl chamber as a sequence of homogenous coordinate tuples,
        h an modulo pi upper triangular matrix in GL(O_inf),
        alpha a unit of K_inf
    such that
        g * M * h * alpha = [s]
    where [s] is the canonical representative of s as a matrix in GL(K_inf)

    i.e. the following should hold:
        PolynomialMatrixToLaurent(g, Kinf) * M * h * alpha eq WeylChamberSimplexToMatrix(s, Kinf)
    Note that due to rounding errors, this equality only holds up to o(PI)-terms
}

    require NumberOfRows(M) eq NumberOfColumns(M) : "Matrix needs to be square.";
    require NumberOfRows(M) le 3 : "Not implemented.";   
    n := NumberOfRows(M);

    Kinf := BaseRing(Parent(M));
    require Type(Kinf) eq RngSerLaur : "Base ring needs to be Laurent series ring.";
    K := BaseRing(Kinf);
    require IsField(K) and IsFinite(K) : "Need to have underlying finite field.";
    R := PolynomialRing(K);

    Oinf := PowerSeriesRingFromLaurent(Kinf);
    PI := UniformizingElement(Kinf);

    // project M onto its corresponding vertex
    g, vertex, h, alpha := WeylChamberVertexDecomposition(M);

    assert2 LaurentEqual(PolynomialMatrixToLaurent(g, Kinf) * M * h * alpha, WeylChamberCoordinatesToMatrix(vertex, Kinf));

    upperTemplate := [i le j-1 select 0 else -1 : j in [1..n], i in [1..n]];
    upperTriags := AllMatricesFromTemplate(#K, Matrix(n,n,upperTemplate) : CheckInvertible := false );
    UnipotentGroup := [IdentityMatrix(Oinf, n) + ChangeRing(U, Oinf) : U in upperTriags];

    for s in [PermutationMatrix(Oinf, p) : p in Sym(n)] do
        for u in UnipotentGroup do

            sigma := s;
            r := u * sigma;
            hNew := h * r;

            // check if r^-1*h^-1 lies in Iwahori subgroup
            if &and{IsWeaklyZero(x) or (Valuation(x) ge 1) where x is hNew[i,j]: i,j in [1..n] | i gt j} then                

                L := WeylChamberCoordinatesToMatrix(vertex, Kinf);

                assert2 LaurentMatrixIsPolynomial(L * u * L^-1);
                gNew := LaurentMatrixToPolynomial(L * u * L^-1)^-1 * g;

                // change to canonical chosen orbit if necessary
                canonicalPermutations := [PermutationMatrix(Kinf, p) : p in PermutationsAtVertex(vertex)];
                if sigma notin canonicalPermutations then
                    for sigmaNew in canonicalPermutations do
                        gamma := L * sigmaNew * ChangeRing(sigma, Kinf)^-1 * L^-1;
                        if LaurentMatrixIsPolynomial(gamma) then
                            sigma := sigmaNew;
                            gNew := LaurentMatrixToPolynomial(gamma) * gNew;
                            break;
                        end if;
                    end for;
                end if;

                simplex := WeylChamberMatrixToSimplex(L * sigma);

                assert2 LaurentEqual(PolynomialMatrixToLaurent(gNew, Kinf) * M * hNew * alpha, L * sigma);
                assert2 LaurentEqual(PolynomialMatrixToLaurent(gNew, Kinf) * M * hNew * alpha, WeylChamberSimplexToMatrix(simplex, Kinf));

                return gNew, simplex, hNew, alpha;
            end if;
        end for;
    end for;

    error "Failed to decompose simplex", vertex, "alpha=", alpha, "g=", g, "h=", h, "M=", M;
end intrinsic;

intrinsic WeylChamberCoordinatesToMatrix(coord::Tup, Kinf::RngSerLaur) -> Mtrx
{
    Given homogenized coordinates (x1,..,xn), return the canconincal representative 
    in GL(K_inf), diag(1,pi^x1,...,pi^xn)
}
    PI := UniformizingElement(Kinf);
    return DiagonalMatrix(Kinf, [1] cat [PI^i : i in coord]);
end intrinsic;

intrinsic WeylChamberCoordinatesToMatrix(coord::Tup, Quot::FldFunRat) -> Mtrx
{
    Given homogenized coordinates (x1,..,xn), return the canconincal representative 
    in GL(F_q(T)), diag(1,T^-x1,...,T^-xn)
}
    return DiagonalMatrix(Quot, [1] cat [Quot.1^-i : i in coord]);
end intrinsic;

intrinsic PermutationsAtVertex(vertex:Tup) -> SetEnum
{
    
}
    d := #vertex;
    require d in {1,2} : "Not implemented";

    SymGrp := Sym(d+1);
    if d eq 1 then
        if vertex[1] eq 0 then
            return {SymGrp ! 1};
        else
            return Set(SymGrp);
        end if;
    else
        j,k := Explode(vertex);

        if j eq 0 and k eq 0 then
            return {SymGrp ! 1};
        elif j eq 0 then
            return {SymGrp ! 1, SymGrp ! [1,3,2], SymGrp ! [2,3,1]};
        elif j eq k then
            return {SymGrp ! 1, SymGrp ! [2,1,3], SymGrp ! [3,1,2]};
        else
            return Set(SymGrp);
        end if;
    end if;
end intrinsic;

intrinsic WeylChamberNonOrientedSimplexToMatrix(simplex::SetEnum[Tup], Kinf::RngSerLaur) -> Mtrx
{}
    PI := UniformizingElement(Kinf);
    flag := Sort(SetToSequence(simplex));
    if (#flag gt 2) and ((flag[2][1] - flag[1][1]) eq 1) then
        v := flag[1];
        v[2] -:= 1;
        return WeylChamberCoordinatesToMatrix(v, Kinf) * Matrix(Kinf, 3, 3, [0,PI^-1,0, 1,0,0, 0,0,1]);
    else
        return WeylChamberCoordinatesToMatrix(flag[1], Kinf);
    end if;
end intrinsic;

intrinsic WeylChamberSimplexToMatrix(simplex::SeqEnum[Tup], Kinf::RngSerLaur) -> Mtrx
{
    Given an ordered sequence of homogenized coordinates representing a maximal simplex, return its
    canonical representative in GL(K_inf)
}
    d := #simplex[1];

    v := WeylChamberCoordinatesToMatrix(simplex[1], Kinf);

    // find orientation by testing
    Perm := PermutationsAtVertex(simplex[1]);

    // TODO remove call to WeylChamberMatrixToSimplex
    for s in [PermutationMatrix(Kinf, p) : p in Perm] do
        if WeylChamberMatrixToSimplex(v*s) eq simplex then
            return v*s;
        end if;
    end for;

    assert false;
end intrinsic;

intrinsic HeckeLeftCosets(P::RngUPolElt, d::RngIntElt, k::RngIntElt) -> SeqEnum[Mtrx]
{
    Return representants S_i such that the double coset Gamma_0(N) diag(1,..,1,P,..,P) Gamma_0(N)
    is the disjoint union of the Gamma_0(N)*S_i
        diag(1,..,1,P,..,P) is a d+1 x d+1 matrix where P appears k times
        P and N need to be coprime
    The result will be matrices in F_q(T)
}

    require d in {1,2} : "Not implemented.";
    require k le d : "k needs to be smaller than d.";

    R := Parent(P);
    q := #BaseRing(R);
    polynomials := PolynomialsUptoDegree(q, Degree(P) - 1);

    S := LaurentSeriesRing(BaseRing(R));
    Quot := FieldOfFractions(R);    

    if d eq 1 then
        result := [ DiagonalMatrix(R, [P, 1]) ];
        result cat:= [ Matrix(R, d+1, d+1, [1, S, 0, P]) : S in polynomials ];
    else
        if k eq 1 then
            result := [ DiagonalMatrix(R, [P, 1, 1]) ];
            result cat:= [ Matrix(R, d+1, d+1, [1, S, 0,  0, P, 0,  0, 0, 1]) : S in polynomials ];
            result cat:= [ Matrix(R, d+1, d+1, [1, 0, S,  0, 1, T,  0, 0, P]) : S, T in polynomials ];      
        else
            result := [ DiagonalMatrix(R, [P, P, 1]) ];
            result cat:= [ Matrix(R, d+1, d+1, [P, 0, 0,  0, 1, S,  0, 0, P]) : S in polynomials ];
            result cat:= [ Matrix(R, d+1, d+1, [1, S, T,  0, P, 0,  0, 0, P]) : S, T in polynomials ];       
        end if;
    end if;

    result := [ ChangeRing(M, Quot) : M in result ];
    return result;
end intrinsic;