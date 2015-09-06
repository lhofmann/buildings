/*
 * Copyright (c) 2015 Lutz Hofmann
 * Licensed under the MIT license, see LICENSE.txt for details.
 */

freeze;
declare verbose harmonicCochains, 1;

vertexData := recformat < 
    type : MonStgElt, // "condition" or "value"
    index : RngIntElt, // index, counted separately for condition and value vertices

    simplex : SetEnum, // corresponding simplex in Weyl chamber
    pointedSimplex : SeqEnum, // oriented simplex
    coset : RngIntElt, // corresponding index in double coset
    weight: RngIntElt, // size of stabilizer

    hasValue : BoolElt,  // indicates whether value is assigned, if type is "value"
    value : RngIntElt,  // value of cochain, if type is "value"
    deleted : BoolElt  // marker to remove value node
>;

harmonicGraph := recformat < 
    G : Grph,            // bipartite graph on vertices Values and Conditions
    Values : SeqEnum,    // d-simplices as nodes in G with Labels vertexData
    Conditions : SeqEnum // (d-1) simplices as nodes in G with Labels vertexData
>;

harmonicSpace := recformat <
    quotient : Rec, // building quotient
    harmonicGraph : Rec, // harmonicGraph structure
    module : ModTupRng, // module of harmonic cochains
    basis : SeqEnum // basis of module of harmonic cochains
>;

intrinsic HarmonicCochainSpace(quotient::Rec) -> Rec
{}
    harmonicGraph := MaximalSimplexGraph(quotient);
    M := hgLinearSystem(harmonicGraph);
    cochainSpace := Kernel(M);
    basis := Basis(cochainSpace);

    return rec< harmonicSpace |
        quotient := quotient,
        harmonicGraph := harmonicGraph,
        module := cochainSpace,
        basis := basis
    >;
end intrinsic;

intrinsic MaximalSimplexGraph(quotient::Rec) -> Rec
{}
    d := quotient`d;

    maxSimplices :=  { <s,i> : i in [1..#quotient`simplex[s]`cosets], s in Keys(quotient`simplex) | #s eq d+1 };
    faceSimplices := { <s,i> : i in [1..#quotient`simplex[s]`cosets], s in Keys(quotient`simplex) | #s eq d };

    graphVertices := maxSimplices join faceSimplices;

    graphEdges := { {simplex, <face, quotient`simplex[simplex[1]]`faces[face][simplex[2]]>} 
                    : face in Subsets(simplex[1], d), simplex in maxSimplices };    

    G := Graph< graphVertices | graphEdges >;

    maxSimplices := SetToSequence(maxSimplices);
    faceSimplices := SetToSequence(faceSimplices);

    function GammaFixgrpSize(quotient, simplex, gammaRep)
        gamma0fixgroup := Gamma0SimplexFixgroup(quotient`q, SetToSequence(simplex));
        gammaRepInv := gammaRep^-1;
        return &+[ 1 : gamma in gamma0fixgroup | quotient`subgroupCondition(gammaRep * gamma * gammaRepInv) ];
    end function;

    for index := 1 to #maxSimplices do
        s, i := Explode(maxSimplices[index]);
        pointed := Sort(SetToSequence(s));        
        data := rec< vertexData | 
            type := "value",
            index := index,
            simplex := s, coset := i,
            pointedSimplex := pointed,
            weight := GammaFixgrpSize(quotient, s, QuotientMatrixRepresentative(quotient, s, i)),
            hasValue := false, 
            value := 0,
            deleted := false >;
        AssignLabel(Vertices(G) ! maxSimplices[index], data);
    end for;

    for index := 1 to #faceSimplices do
        s, i := Explode(faceSimplices[index]);
        pointed := Sort(SetToSequence(s));
        data := rec< vertexData | 
            type := "condition",
            index := index,
            simplex := s, coset := i,
            weight := GammaFixgrpSize(quotient, s, QuotientMatrixRepresentative(quotient, s, i)),
            pointedSimplex := pointed >;         
        AssignLabel(Vertices(G) ! faceSimplices[index], data);
    end for;

    return rec< harmonicGraph |
        G := G,
        Values := ChangeUniverse(maxSimplices, Vertices(G)),
        Conditions := ChangeUniverse(faceSimplices, Vertices(G))
    >;
end intrinsic;

intrinsic hgSetValue(vertex::GrphVert, value::RngIntElt : hasValue := true)
{}
    require Label(vertex)`type eq "value" : "Can't assign value to condition node.";

    data := Label(vertex);
    data`hasValue := hasValue;
    data`value := value;
    AssignLabel(vertex, data);
end intrinsic;

intrinsic hgFreeParameters(vertex::GrphVert) -> RngIntElt
{}
    require Label(vertex)`type eq "condition" : "Vertex needs to be condition node.";

    return {u : u in Neighbours(vertex) | (not Label(u)`hasValue) and (not Label(u)`deleted)};
end intrinsic;

intrinsic harmonicSign(simplex::SeqEnum, face::SeqEnum) -> RngIntElt
{}
    pivot := face[1];
    k := #simplex - 1;

    // find position of distinguished vertex in lattice flag
    i := Index(simplex, pivot) - 1;
    assert i ge 0;
    sign := k*(k-i+1) mod 2;  // note: if i=0, this is always 0
    return (-1)^sign;
end intrinsic;

intrinsic harmonicSign(simplex::GrphVert, face::GrphVert) -> RngIntElt
{}
    return harmonicSign(Label(simplex)`pointedSimplex, Label(face)`pointedSimplex);
end intrinsic;

intrinsic hgConditionSum(vertex::GrphVert) -> RngIntElt
{}
    require Label(vertex)`type eq "condition" : "Vertex needs to be condition node.";

    neighbours := {u : u in Neighbours(vertex) | Label(u)`hasValue and (not Label(u)`deleted)};
    if #neighbours eq 0 then
        return 0;
    else
        return &+[harmonicSign(u, vertex)*Label(u)`value : u in neighbours];
    end if;
end intrinsic;

intrinsic hgMarkAsDeleted(vertex::GrphVert : value := true)
{}
    require Label(vertex)`type eq "value" : "Can't mark condition node.";

    data := Label(vertex);
    data`deleted := value;
    AssignLabel(vertex, data);
end intrinsic;

intrinsic hgVerifyCochain(harmonicGraph::Rec) -> BoolElt
{}
    valid := true;

    for vertex in harmonicGraph`Conditions do
        if hgConditionSum(vertex) ne 0 then
            vprintf harmonicCochains: "Non-zero value (%o) at %o.\n", hgConditionSum(vertex), vertex;
            valid := false;
        end if;
    end for;

    return valid;
end intrinsic;

intrinsic hgResetValues(~harmonicGraph::Rec)
{}
    for vertex in harmonicGraph`Values do
        data := Label(vertex);
        data`hasValue := false;
        data`value := 0;
        data`deleted := false;
        AssignLabel(vertex, data);
    end for;
end intrinsic;

intrinsic hgLinearSystem(harmonicGraph::Rec) -> MtrxSprs
{}
    M := SparseMatrix(Integers());
    for j := 1 to #harmonicGraph`Conditions do
        face := harmonicGraph`Conditions[j];
        neighbours := {simplex : simplex in Neighbours(face) | not Label(simplex)`deleted};        
        for simplex in neighbours do
            assert Label(simplex)`type eq "value";
            assert (Label(face)`weight mod Label(simplex)`weight) eq 0;       

            w := Label(face)`weight / Label(simplex)`weight;            
            SetEntry(~M, Label(simplex)`index, j, harmonicSign(simplex, face) * w);
        end for;
    end for;
    return M;
end intrinsic;

intrinsic hgDoubleCosetOperator(harmonicGraph::Rec, quotient::Rec, leftRepresentants::SeqEnum[Mtrx] : Precision := 200) -> MtrxSprs
{ Return souble coset operator as linear map on harmonicGraph`Values 
    The operator will correspond the the double coset Gamma_0(N) S Gamma_0(N) which is given
    by its disjoint union of left cosets Gamma_0(N) S_i where the S_i are the parameter leftRepresentants
    eg for leftRepresentants = HeckeLeftCosets this will return the corresponding Hecke Operator }

    K := BaseRing(Parent(quotient`N));
    Kinf := LaurentSeriesRing(K : Precision := Precision);
    R := PolynomialRing(K);
    Quot := FieldOfFractions(R);

    M := SparseMatrix(Integers(), #harmonicGraph`Values, #harmonicGraph`Values);

    RationalToLaurent := hom< Quot -> Kinf | Kinf.1^-1 >;

    for j := 1 to #harmonicGraph`Values do
        simplex := Label(harmonicGraph`Values[j])`pointedSimplex;
        coset := Label(harmonicGraph`Values[j])`coset;        
        representant := QuotientMatrixRepresentative(quotient, Set(simplex), coset);

        simplexMatrix := PolynomialMatrixToLaurent(representant, Kinf)*WeylChamberSimplexToMatrix(simplex, Kinf);

        for leftrepresentant in leftRepresentants do
            image := ChangeRing(leftrepresentant, RationalToLaurent) * simplexMatrix;

            g, imageSimplex := WeylChamberSimplexDecomposition(image);
            g := g^-1;

            // assume that if simplex is not in quotient, all harmonic cochains have value zero on this simplex
            if Set(imageSimplex) in Keys(quotient`simplex) then
                gIndex := quotient`reductionFunc(quotient, g);
                imageIndex := quotient`simplex[Set(imageSimplex)]`cosetPointer[gIndex];
                
                assert2 quotient`subgroupCondition(quotient`representatives[gIndex]*g^-1);
                assert gIndex in quotient`simplex[Set(imageSimplex)]`cosets[imageIndex];

                hgVertex := Vertices(harmonicGraph`G) ! <Set(imageSimplex), imageIndex>;
                i := Label(hgVertex)`index;              

                assert Label(hgVertex)`simplex eq Set(imageSimplex);
                assert Label(hgVertex)`coset eq imageIndex;

                M[i,j] := M[i,j] + harmonicSign(imageSimplex, Label(hgVertex)`pointedSimplex);
            end if;
        end for;
    end for;

    return M;
end intrinsic;

intrinsic harDimension(harmonicSpace::Rec) -> RngIntElt
{
    Returns dimension of space of harmonic cochains
}
    return #(harmonicSpace`basis);
end intrinsic;

intrinsic harDoubleCosetOperator(harmonicSpace::Rec, leftRepresentants::SeqEnum[Mtrx] : Precision := 200) -> Mtrx
{
    Compute the transformation matrix of the double coset operator given by leftRepresentants
    Optional parameter Precision determines the precision of the Laurent series ring

    The operator will correspond the the double coset Gamma_0(N) S Gamma_0(N) which is given
    by its disjoint union of left cosets Gamma_0(N) S_i where the S_i are the parameter leftRepresentants
    eg for leftRepresentants = HeckeLeftCosets this will return the corresponding Hecke Operator 
}
    operator := hgDoubleCosetOperator(harmonicSpace`harmonicGraph, harmonicSpace`quotient, leftRepresentants);
    cochainImage := [cochain * operator : cochain in harmonicSpace`basis];
    transformationMatrix := Matrix(Integers(), [ Coordinates(harmonicSpace`module, v) : v in cochainImage | v in harmonicSpace`module ]);

    if NumberOfRows(transformationMatrix) ne harDimension(harmonicSpace) then
        error "Image of double coset operator not in space of harmonic cochains.";
    end if;

    return transformationMatrix;
end intrinsic;

intrinsic harCoordinatesToCochain(harmonicSpace::Rec, vector::ModTupRngElt) -> SeqEnum
{
    Represent a vector in harmonicSpace`module as sequence of Tuples < <simplex, cosetIndex>, value >
        where simplex is the level w of the simplex in the quotient building and cosetIndex corresponds
        to the index of the double coset Gamma \ Gamma_0 / Fix(w)
        and value is the value of the harmonic cochain at this simplex
    Zero values will be omitted
}
    vector := ElementToSequence(vector);
    require #vector eq #(harmonicSpace`harmonicGraph`Values) : "Vector of invalid length.";

    cochain := [ <harmonicSpace`harmonicGraph`Values[i], vector[i]> : i in [1..#vector] | vector[i] ne 0 ];

    return cochain;
end intrinsic;