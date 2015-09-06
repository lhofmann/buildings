/*
 * Copyright (c) 2015 Lutz Hofmann
 * Licensed under the MIT license, see LICENSE.txt for details.
 */

freeze;
declare verbose buildingQuotient, 1;
import "buildingLib.m" : FiniteFldListAddOne;

// quotient building of G \ Gamma0
QuotientBuildingRec := recformat < 
    representatives : SeqEnum,  // a sequence of representatives of G \ Gamma0
    reducedRepresentatives : SeqEnum, // some sort of representatives used by reductionFunc; needs to be same length as representatives
    reductionFunc : UserProgram, // a function that for a matrix in Gamma0 gives an index to its canonical representative
    factorN : SeqEnum, // a factorization of N, given as sequence of polynomials
    q : RngIntElt,
    d : RngIntElt,
    N : RngUPolElt,  // the polynomial defining G
    subgroupCondition : UserProgram,  // returns true if a matrix lies in G
    simplex : Assoc  // SetEunm[Tup] => QuotientComplexRec
                     // for each simplex (a sequence of tuples) in the Weyl Chamber, store a QuotientComplexRec
                     // all simplices in this quotient building can be obtained by Keys(simplex)
>;

// the fiber above a simplex in the Weyl Chamber
QuotientComplexRec := recformat < 
    fixgroup : Mtrx,   // an integer-valued matrix template, defining the Gamma0-Fixgroup
    cosets : SeqEnum,  // the double cosets G \ Gamma0 / fixgroup;
                       // sequence of sequences of indices refering to QuotientBuildingRec`representatives 
    cosetPointer : SeqEnum, // for each representative, a pointer to its coset
    faces : Assoc  // SetEnum[Tup] => SeqEnum[RngIntElt]
                   // this holds the "gluing map" G \ Gamma0 / H -> G \ Gamma0 / H'
                   //  for each face of this simplex, store a sequence of indices
                   //  this sequence has the same length as cosets and each element is a index in the cosets-sequence
                   //  of the corresponding fiber of that face
                   // to get all faces of this vertex, use Keys(faces)
>;

intrinsic QuotientGamma0N(d::RngIntElt, N::RngUPolElt : additionalLevels := 0, useIterator := false) -> Rec
{}
    K := BaseRing(Parent(N));
    require IsField(K) and IsField(K) : "Base ring needs to be finite field.";
    q := #K;

    factor := Factorization(N);
    factorPoly := [factor[i][1]^factor[i][2] : i in [1..#factor]];

    projRep := ProjectiveProductRepresentants(d, factorPoly);
    matrixRep := [ProjectiveToMatrix(r, factorPoly) : r in projRep];

    matrixReduce := function(quotient, M)
        if (Determinant(M) mod quotient`N) ne 1 then
            _, detInv, _ := Xgcd(Determinant(M), quotient`N);            
            M := DiagonalMatrix([detInv] cat [1 : i in [1..quotient`d]]) * M;
        end if;
        reduced := MatrixToProjective(M, quotient`factorN);

        // TODO: replace with binary search
        return Index(quotient`reducedRepresentatives, reduced);
    end function;

    quotient := rec< QuotientBuildingRec |
        representatives := matrixRep,
        reducedRepresentatives := projRep,
        reductionFunc := matrixReduce,
        q := q,
        d := d,
        N := N,
        factorN := factorPoly,
        subgroupCondition := func< g | IsGamma0NElement(g, N) >,
        simplex := AssociativeArray()
    >;

    queue := {StandardSimplex(d)};
    levels := d*d*Degree(N) + 1 + additionalLevels;

    for level := 1 to levels do
        QuotientAddSimplices(~quotient, queue : useIterator := useIterator);
        WeylChamberNextGallery(~queue);
        queue := queue diff Keys(quotient`simplex);
    end for;

    return quotient;
end intrinsic;

intrinsic IsValidWeylSimplex(simplex::SeqEnum[Tup]) -> BoolElt
{
    Given a sequence of vertices, checks if this is a simplex in the Weyl Chamber.
}

    require &and[ #simplex[i] eq #simplex[i+1] : i in [1..#simplex-1] ] : "Coordinates need to be of same length";
    require #simplex gt 0 : "Need at least one coordinate";

    d := #simplex[1];

    // check each vertex
    if not &and[ vertex[i] ge 0 : i in [1..#vertex], vertex in simplex ] or
       not &and[ vertex[i] le vertex[i+1] : i in [1..#vertex-1], vertex in simplex ] then
        return false;
    end if;

    // check if the lattices can be aligned such that L < L' < L'' < ... < pi*L
    // if there is such an order, it needs to be the lexicographic ordering on the homogenous coordinates
    simplex := Sort(simplex);
    if not &and[ simplex[i][j] le simplex[i+1][j] : i in [1..#simplex-1], j in [1..d] ] then
        return false;
    end if;

    // check if the last inclusion .. < ... < pi*L holds
    if not &and[ lastVertex[i] le firstVertex[i]+1 
                    where lastVertex is simplex[#simplex]
                    where firstVertex is simplex[1]
                 : i in [1..d] ] then
        return false;
    end if;

    return true;
end intrinsic;

intrinsic WeylChamberNeighbors(vertex::Tup) -> SetEnum[SetEnum[Tup]], SetEnum[Tup]
{ 
    Given a vertex of the Weyl Chamber, return a sequence of all incident d-simplices 
    and a sequence of all incident vertices inside the Weyl Chamber *in positive direction*.
    The vertex itself is not returned.

    *In positive direction* means that all coordinates of all vertices involved differ by at most a positive number.
}

    d := #vertex;

    neighbors := {};
    hasNext := true;
    // all possible neighbors can be reached by adding 1 to some of its coordinates
    coordinateDiff := [GF(2)| 0 : i in [1..d]];
    repeat
        nextVertex := <vertex[i] + (Integers() ! coordinateDiff[i]) : i in [1..d]>;
        if IsValidWeylSimplex([nextVertex]) then
            Include(~neighbors, nextVertex);
        end if;
        FiniteFldListAddOne(~coordinateDiff, ~hasNext);
    until not hasNext;

    // get incident d-simplices by trying all combinations
    maxSimplices := {};
    for simplex in Subsets(neighbors, d+1) do
        if IsValidWeylSimplex(SetToSequence(simplex)) then
            Include(~maxSimplices, simplex);
        end if;
    end for;

    Exclude(~neighbors, vertex);

    return maxSimplices, neighbors;
end intrinsic;

intrinsic QuotientAddSimplex(~quotient::Rec, simplex::SetEnum[Tup] : useIterator := false)
{
    Add a simplex and recursively all its faces to quotient building

    If useIterator is set to false (default), the fixgroups will be enumerated completely,
    otherwise they will be iteratively generated (slower but less memory consumption)

    If the simplex already is contained in the data structure, it will be skipped, but its faces still be processed.
}

    if simplex notin Keys(quotient`simplex) then        
        vprintf buildingQuotient: "Level %o\t", simplex;

        // make fixgroup template
        fixgroup := Gamma0SimplexFixgroupTemplate(SetToSequence(simplex));
        fixgroup := Gamma0SimplexFixgroupTemplateReduce(fixgroup, Degree(quotient`N));

        // find simplex whose fixgroup is contained in our fixgroup
        candidates := [s : s in Keys(quotient`simplex) 
                         | simplex subset s or Gamma0SubgroupIsContained(quotient`simplex[s]`fixgroup, fixgroup)];
        equalFixGrp := [s : s in candidates | Gamma0SubgroupEqual(quotient`simplex[s]`fixgroup, fixgroup)];      

        // if already one fixgroup is equal to ours, just copy those cosets
        if #equalFixGrp gt 0 then                    
            cosets := quotient`simplex[equalFixGrp[1]]`cosets;  
            cosetPointer := quotient`simplex[equalFixGrp[1]]`cosetPointer;
        else
            cosets := [];
            cosetPointer := [];

            if #candidates gt 0 then
                // sort by number of classes and choose the one with the least (thus biggest) classes
                Sort(~candidates, func< x,y | #quotient`simplex[x]`cosets - #quotient`simplex[y]`cosets >);
                cosets := quotient`simplex[candidates[1]]`cosets;
                cosetPointer := quotient`simplex[candidates[1]]`cosetPointer;
                vprintf buildingQuotient: "%o => ", #cosets;

                // TODO: compute quotients of the two fixgroups and use a set of representatives as fixgroupSet instead
            else
                vprintf buildingQuotient: "%o => ", #quotient`representatives;
            end if;

            if useIterator then
                fixgroupSet := AllMatricesFromTemplate_Iterator(quotient`q, fixgroup : CheckInvertible := true);
            else
                fixgroupSet := Gamma0SubgroupFromTemplate(quotient`q, fixgroup);
            end if;

            if assigned quotient`reductionFunc then
                cosets, cosetPointer := QuotientRightCosets(quotient, cosets, cosetPointer, fixgroupSet);
            else
                cosets := CongruenceSubgroupDoubleCosets(quotient`subgroupCondition, quotient`representatives, cosets, fixgroupSet, "right");
            end if;
        end if;
        vprintf buildingQuotient: "%o\n", #cosets;
        quotient`simplex[simplex] := rec< QuotientComplexRec | 
            fixgroup := fixgroup, 
            cosets := cosets,
            cosetPointer := cosetPointer,
            faces := AssociativeArray() >;
    end if;
    // add all faces
    if #simplex gt 1 then
        for face in Subsets(simplex, #simplex - 1) do
            QuotientAddSimplex(~quotient, face : useIterator := useIterator);
        end for;
    end if;
end intrinsic;

intrinsic QuotientAssignFaces(~quotient::Rec, simplex::SetEnum[Tup])
{
    Compute the faces data for a given simplex in the quotient.
    Recursively computes the data for the faces of its faces.
    This computes the "gluing map" G \ Gamma0 / H -> G \ Gamma0 / H'
}

    if #simplex gt 1 then        
        for face in Subsets(simplex, #simplex - 1) do
            numCosets := #quotient`simplex[simplex]`cosets;

            // find indices for each coset (<-> element in the fiber)
            faceIndexList := [0 : i in [1..numCosets]];
            for i := 1 to numCosets do
                coset := Set(quotient`simplex[simplex]`cosets[i]);

                if assigned quotient`reductionFunc then
                    faceIndexList[i] := quotient`simplex[face]`cosetPointer[ Representative(coset) ];
                else
                    // try all cosets in the fiber of the face and check if our coset is contained in one
                    // it will always be contained in one of those
                    k := 0;
                    while k lt #quotient`simplex[face]`cosets do
                        k +:= 1;
                        if coset subset Set(quotient`simplex[face]`cosets[k]) then
                            faceIndexList[i] := k;
                            break;
                        end if;
                    end while;    
                end if;   
            end for;
            quotient`simplex[simplex]`faces[face] := faceIndexList;

            // assign faces of faces
            QuotientAssignFaces(~quotient, face);
        end for;
    end if;    
end intrinsic;

intrinsic WeylChamberNextLevel(~queue::SetEnum[Tup], ~simplices::SetEnum)
{
    Iterate over weyl chamber highest dimensional simplices by slices of vertices

    queue holds the current set of vertices, neighboring simplices in positive direction only
    are stored in parameter simplices

    In each call of WeylChamberNextLevel, all simplices that contain any vertex in queue as one of their
    left-most vertices will be returned in parameter simplices. Then, all vertices of those simplices which 
    are not in queue will be returned as new queue.

    Example:
    queue := [StandardVertex(d)];
    simplices := [];
    for level := 1 to levels do
        WeylChamberNextLevel(~queue, ~simplices);
        QuotientAddSimplices(~quotient, simplices);
    end for;
}
    nextLevel := {};
    levelSimplices := {};

    // get all incident d-simplices and adjacent vertices
    for vertex in queue do
        simplices, nextVertices := WeylChamberNeighbors(vertex);
        levelSimplices := levelSimplices join simplices;
        nextLevel := nextLevel join (nextVertices diff queue);
    end for;

    queue := nextLevel;
    simplices := levelSimplices;
end intrinsic;

intrinsic WeylChamberNextGallery(~queue::SetEnum)
{
    Iterate over weyl chmaber breadth-first in terms of galleries.
    In each iteration, all simplices have the same gallery-distance from the standard simplex.    

    queue holds the maximal simplices in each iteration.

    Example:
    queue := [StandardSimplex(d)];
    for level := 1 to levels do        
        QuotientAddSimplices(~quotient, queue);
        WeylChamberNextGallery(~queue);

        WORKAROUND/BUG: might return some simplices of previous level
        queue := queue diff Keys(quotient`simplex);
    end for;    
}

    d := #Representative(queue) - 1;

    nextLevel := {};

    for simplex in queue do
        // get neighbors that have a vertex in common
        neighbors := &join[ WeylChamberNeighbors(vertex) : vertex in simplex ];
        // only select neighbors that also have a face in common
        neighbors := { neighbor : neighbor in neighbors
                                | &or[ face subset simplex : face in Subsets(neighbor, d) ] };
        nextLevel := nextLevel join neighbors;
    end for;

    queue := nextLevel diff queue;
end intrinsic;

intrinsic QuotientAddSimplices(~quotient::Rec, simplices::SetEnum[SetEnum[Tup]] : useIterator := false)
{
    Add all simplices and their faces given as parameter to quotient, compute gluing data.

    If useIterator is set to true, all fixgroups will be iteratively enumerated (see QuotientAddSimplex)
}

    // compute double cosets and gluing data
    for simplex in simplices do
        QuotientAddSimplex(~quotient, simplex : useIterator := useIterator);
        QuotientAssignFaces(~quotient, simplex);
    end for;
end intrinsic;

intrinsic QuotientNonSimplicialData(quotient::Rec) -> SeqEnum
{
    Returns a sequence of gluing data which is non-simplicial.
    If the list is empty, the quotient is simplicial.

    Returns a sequence of tuples !!TODO better data strucutre
        <simplex, number of times faceA and faceB are glued, faceA, index of faceA, faceB, index of faceB>
}

    result := [];
    for simplex in Keys(quotient`simplex) do
        if #simplex le 1 then
            continue;
        end if;

        for facePair in Subsets(Keys(quotient`simplex[simplex]`faces), 2) do
            faceA, faceB := Explode(SetToSequence(facePair));

            numGlue := AssociativeArray();

            // count how often the faces are glued to the same element in the respective fibers
            for i := 1 to #quotient`simplex[simplex]`cosets do
                glue := <quotient`simplex[simplex]`faces[faceA][i], quotient`simplex[simplex]`faces[faceB][i]>;
                if glue in Keys(numGlue) then
                    Append(~(numGlue[glue]), i);
                else
                    numGlue[glue] := [i];
                end if;
            end for;

            // if any two faces are glued twice or more to the same elements in the respective fibers,
            // the quotient is non-simplicial
            for glue in Keys(numGlue) do
                if #numGlue[glue] gt 1 then
                    Append(~result, <simplex, numGlue[glue], faceA, glue[1], faceB, glue[2]>);
                end if;
            end for;
        end for;
    end for;
    return result;
end intrinsic;

intrinsic QuotientCusp(quotient::Rec) -> SeqEnum, SeqEnum
{ Returns all maximal simplices in quotient that belong to its cusp 

    Optional parameter traverse (default: "galleries") can either be "vertices" or "galleries".
        Specifies the method to traverse the Weyl chamber.
        "vertices" will use WeylChamberNextLevel, thus walking through the Weylchamber by slices of vertices
        "galleries" will use WeylChamberNextGallery, thus walking by galleries
}
    require quotient`d in {1,2} : "Not implemented.";

    n := Maximum(2, Degree(quotient`N));
    if quotient`d eq 2 then        
        compactVertices := { <j,k> : k in [j..j+n-1], j in [0..n-1]};
    elif quotient`d eq 1 then
        compactVertices := { <i> : i in [0..n-1] };
    end if;
    assert &and{ {v} in Keys(quotient`simplex) : v in compactVertices };
    
    compactSimplices := { s : s in Keys(quotient`simplex) | (#s eq quotient`d+1) and s subset compactVertices };
    cuspSimplices := { s : s in Keys(quotient`simplex) | (#s eq quotient`d+1) and s notsubset compactVertices };

    return cuspSimplices, compactSimplices;
end intrinsic;

intrinsic InducedSubQuotient(quotient::Rec, simplices::SetEnum[SetEnum[Tup]]) -> Rec
{ Return sub-quotient induced by set of simplices (for each simplex take all edges and edges of edges etc.) }

    subquotient := quotient;
    subquotientSimplices := &join{ Subsets(simplex) : simplex in simplices };

    for simplex in Keys(subquotient`simplex) do
        if simplex notin subquotientSimplices then
            Remove(~subquotient`simplex, simplex);
        end if;
    end for;

    return subquotient;
end intrinsic;

/*
    function QuotientRepresentative(quotient, simplex, coset)
        repIndex := Representative(quotient`simplex[simplex]`cosets[coset]);
        representant := quotient`representatives[repIndex];
        return representant;
    end function;
*/
intrinsic QuotientMatrixRepresentative(quotient::Rec, simplex::SetEnum[Tup], cosetIndex::RngIntElt) -> Mtrx
{
    Given a simplex w in the Weylchamber (the level of the simplex in the quotient building) and an index referring
    to the double coset Gamma \ Gamma_0 / Fix(w), return a matrix representant
}
    require simplex in Keys(quotient`simplex) : "Simplex not in building.";
    requirerange cosetIndex, 1, #(quotient`simplex[simplex]`cosets);

    repIndex := quotient`simplex[simplex]`cosets[cosetIndex][1];
    return quotient`representatives[repIndex];
end intrinsic;

//
//  Export functions
//

makeSimplexName := function(simplex)
    simplexName := &cat[ Sprint(vertex) : vertex in simplex ];
    simplexName := &cat[ c : c in ElementToSequence(simplexName) | c ne " " ];
    return simplexName;
end function;

intrinsic QuotientToDeltaComplex(quotient::Rec) -> MonStgElt
{
    Returns sage DeltaComplex data as a string
}
    sageSimplex := function(simplex, level, dim)
        s := "Simplex([";
        for i := 1 to dim do
            s *:= Sprintf("'%o#%o#%o',", makeSimplexName(simplex), level, i);
        end for;            
        s *:= "])";
        return s;
    end function;

    s := "{\n";
    for simplexKey in Keys(quotient`simplex) do
        simplex := Sort(SetToSequence(simplexKey));

        for i := 1 to #quotient`simplex[simplexKey]`cosets do
            line := "\t" * sageSimplex(simplex, i, #simplex) * ":\n\t\t[";
            if #simplex gt 1 then
                for j := #simplex to 1 by -1 do
                    face := Remove(simplex, j);
                    faceKey := Set(face);
                    k := quotient`simplex[simplexKey]`faces[faceKey][i];
                    line *:= sageSimplex(face, k, #face) * ",\n\t\t ";
                end for;            
            end if;    
            line *:= "],\n";
            s *:= line;
        end for;
    end for;
    s *:= "\n}";
    return s;
end intrinsic;

intrinsic QuotientToDotGraph(quotient::Rec) -> MonStgElt
{
    Returns a GraphViz dot file describing the underlying graph of the quotient
}

    s := "digraph G {\n\trankdir=LR;\n\tranksep=2;\n//\tnode [shape=point];\n\tedge [dir=none];\n";

    vertices := &join(Keys(quotient`simplex));
    vertices := Sort(SetToSequence(vertices));

    // try to put all fibers onto one column
    for vertex in vertices do
        s *:= "\t{\trank = same;\n\t\t";
        for i := 1 to #quotient`simplex[{vertex}]`cosets do
            s *:= Sprintf("\"%o#%o\"; ", makeSimplexName({vertex}), i);
        end for;
        s *:= "\t}\n";
    end for;

    for simplex in Keys(quotient`simplex) do
        if #simplex eq 2 then
            for i := 1 to #quotient`simplex[simplex]`cosets do
                s *:= "\t";
                first := true;
                for vertex in Sort(SetToSequence(simplex)) do
                    k := quotient`simplex[simplex]`faces[{vertex}][i];;
                    s *:= Sprintf("\"%o#%o\"", makeSimplexName({vertex}), k);

                    if first then
                        first := false;
                        s *:= " -> ";
                    end if;
                end for;
                s *:= ";\n";
            end for;
        end if;
    end for;

    s *:= "}\n";
    return s;
end intrinsic;

// compute spring layout by calling graphlayout.py
function PythonSpringLayout(quotient, vertices, OptimizationSteps)
    coordinates := AssociativeArray();
    for vertex in vertices do
        coordinates[vertex] := [<0.0,0.0,0.0> : i in [1..#quotient`simplex[{vertex}]`cosets]];
    end for;    

    // create edge list
    graphData := "";
    edges := {s : s in Keys(quotient`simplex) | #s eq 2};
    for edge in edges do
        for i := 1 to #quotient`simplex[edge]`cosets do
            for vertex in Keys(quotient`simplex[edge]`faces) do
                graphData *:= Sprintf("%o%o ", makeSimplexName(vertex), quotient`simplex[edge]`faces[vertex][i]);
            end for;
            graphData *:= "\n";
        end for;
    end for;

    // call python script
    tempInputFilename := Tempname("temp/_edge_list.temp");
    tempOutputFilename := Tempname("temp/_layout.temp");

    WriteBinary(tempInputFilename, BinaryString(graphData) : Overwrite := true);
    res := System(Sprintf("python lib/graphlayout.py %o %o -i %o -d 3", tempInputFilename, tempOutputFilename, OptimizationSteps));
    assert res eq 0;

    contents := Read(tempOutputFilename);
    lines := Split(contents, "\n");
    for line in lines do        
        validLine, _, parsed := Regexp("<([0-9]+),([0-9]+)>([0-9]+) ([0-9\\.]+) ([0-9\\.]+) ([0-9\\.]+)", line);

        if not validLine then
            continue;
        end if;

        parsed := [eval(p) : p in parsed];        

        vertex := <Integers() ! parsed[1], Integers() ! parsed[2]>;
        index := Integers() ! parsed[3];
        pos := <RealField() ! parsed[4], RealField() ! parsed[5], RealField() ! parsed[6]>;

        coordinates[vertex][index] := pos;
    end for;

    return coordinates;
end function;

// quick-and-dirty O(n^2) implementation of the Fruchterman-Reingold Spring Layout
function SpringLayout(quotient, vertices, OptimizationSteps, RestrictToSpheres)
    coordinates := AssociativeArray();
    for vertex in vertices do
        coordinates[vertex] := [<0.0,0.0,0.0> : i in [1..#quotient`simplex[{vertex}]`cosets]];
    end for;    

    maxNumCosets := Maximum({#quotient`simplex[{vertex}]`cosets : vertex in vertices});
    for vertex in vertices do
        for i := 1 to #quotient`simplex[{vertex}]`cosets do
            if quotient`d eq 1 then
                x := vertex[1];
                y := i - 1/2 * #quotient`simplex[{vertex}]`cosets;
                z := 0;            
            elif quotient`d eq 2 then
                x, y := Explode(vertex);
                y := y-x/2;
                x := x*Sqrt(3)/2;
                z := (i - 1/2 * #quotient`simplex[{vertex}]`cosets) * Sqrt(3)/2;                
            else
                x, y, z := Explode(vertex);
                y := y-x/2;
                x := x*Sqrt(3)/2;
                //z := ((i - 1/2) * (maxNumCosets / #quotient`simplex[{vertex}]`cosets)) * Sqrt(3)/2 + z * maxNumCosets;
                z := (i - 1/2 * #quotient`simplex[{vertex}]`cosets) * Sqrt(3)/2 + z * maxNumCosets;
            end if;

            coordinates[vertex][i] := <x, y, z>;
        end for;
    end for;

    if OptimizationSteps gt 0 then

        // Fruchterman, Reingold: Graph Drawing by Force-directed Placement (1991)

        vertexRec := recformat < vertex: Tup, index: RngIntElt >;
        dist := function(v, w)
            return &+[(v[i]-w[i])^2 : i in [1..#v]];
        end function;

        velocity := AssociativeArray();
        for vertex in vertices do
            velocity[vertex] := [<0.0,0.0,0.0> : i in [1..#quotient`simplex[{vertex}]`cosets]];        
        end for;

        // get neighbors per vertex
        neighbors := AssociativeArray();
        for vertex in vertices do
            numCosets := #quotient`simplex[{vertex}]`cosets;
            nbs := [ [] : i in [1..numCosets] ];
            for vertexNeighbor in vertices do
                if vertexNeighbor eq vertex then
                    continue;
                end if;

                oneSimplex := {vertex, vertexNeighbor};
                if oneSimplex notin Keys(quotient`simplex) then
                    continue;
                end if;

                for k := 1 to #quotient`simplex[oneSimplex]`cosets do
                    i := quotient`simplex[oneSimplex]`faces[{vertex}][k];
                    j := quotient`simplex[oneSimplex]`faces[{vertexNeighbor}][k];
                    Append(~(nbs[i]), rec<vertexRec| vertex := vertexNeighbor, index := j>);
                end for;
            end for;
            neighbors[vertex] := nbs;
        end for;

        for nIter := 1 to OptimizationSteps do
            vprintf buildingQuotient: "Optimization %o/%o\n", nIter, OptimizationSteps;

            for vertex in vertices do
                for i := 1 to #quotient`simplex[{vertex}]`cosets do
                    force := <0.0,0.0,0.0>;
                    for other in vertices do
                        for j := 1 to #quotient`simplex[{other}]`cosets do
                            if (vertex eq other) and (i eq j) then
                                continue;
                            end if;
                            distSq := dist(coordinates[vertex][i], coordinates[other][j]);
                            if distSq lt 10^2 then
                                force := < force[k] + 0.1 * (coordinates[vertex][i][k] - coordinates[other][j][k])/distSq : k in [1..3] >;
                            end if;
                        end for;
                    end for;

                    for neighbor in neighbors[vertex][i] do              
                        force := < force[k] + 0.06*(coordinates[neighbor`vertex][neighbor`index][k] - coordinates[vertex][i][k]) : k in [1..3] >;
                    end for;

                    velocity[vertex][i] := < (velocity[vertex][i][k] + force[k])*0.85 : k in [1..3] >;
                end for;
            end for;

            for vertex in vertices do
                for i := 1 to #quotient`simplex[{vertex}]`cosets do
                    coordinates[vertex][i] := < coordinates[vertex][i][k] + velocity[vertex][i][k] : k in [1..3] >;

                    if RestrictToSpheres then
                        norm := Sqrt(&+[ coordinates[vertex][i][k]^2 : k in [1..3] ]);
                        coordinates[vertex][i] := < coordinates[vertex][i][k] / norm * 2 * (1 + vertex[2]) : k in [1..3] >;
                    end if;                     
                end for;             
            end for;
        end for;
    end if;

    return coordinates;
end function;

intrinsic QuotientToJavaView(quotient::Rec : OptimizationSteps := 0, RestrictToSpheres := false, Python := true) -> MonStgElt
{
    Returns a JavaView file of the underlying sceleton of 2-simplices as a string.
    Colors are chosen at random per coset; equal cosets have equal colors.
    If OptimizationSteps > 0, will run a force-directed graph layout.
}

    require quotient`d in [1,2,3] : "Not implemented";

    function RandomColor()
        mix := < 255, 255, 255 >;
        c := < ((Random(255) + mix[i]) div 2) mod 256 : i in [1..3] >;
        return &cat[ Sprint(c[i]) cat " " : i in [1..2] ] cat Sprint(c[#c]);
    end function;

    s := "<?xml version=\"1.0\" encoding=\"ISO-8859-1\" standalone=\"no\"?>
<!DOCTYPE jvx-model SYSTEM \"http://www.javaview.de/rsrc/jvx.dtd\">
<jvx-model>
\t<geometries>
\t\t<geometry>
\t\t\t<pointSet point=\"show\" color=\"show\" dim=\"3\">
\t\t\t\t<points>
\t\t\t\t\t<thickness>5.0</thickness>\n";

    vertices := &join(Keys(quotient`simplex));
    vertices := Sort(SetToSequence(vertices));

    if #vertices eq 0 then
        vprint buildingQuotient: "Warning: Saving empty data to JavaView.";
        return "";
    end if;

    // setup indices for each vertic in the quotient
    indices := AssociativeArray();
    index := 0;
    for vertex in vertices do
        indices[vertex] := [-1 : i in [1..#quotient`simplex[{vertex}]`cosets]];
        for i := 1 to #quotient`simplex[{vertex}]`cosets do
            indices[vertex][i] := index;
            index := index + 1;
        end for;
    end for;


    // compute spring layout
    if Python then
        coordinates := PythonSpringLayout(quotient, vertices, OptimizationSteps);
    else
        coordinates := SpringLayout(quotient, vertices, OptimizationSteps, RestrictToSpheres);
    end if;

    // distribute colors for each vertex
    colors := [];
    cosetColor := AssociativeArray();
    for vertex in vertices do
        for i := 1 to #quotient`simplex[{vertex}]`cosets do
            coset := Set(quotient`simplex[{vertex}]`cosets[i]);
            if coset notin Keys(cosetColor) then
                cosetColor[coset] := RandomColor();                
            end if;
            Append(~colors, cosetColor[coset]);
        end for;
    end for;

    // output vertex data
    pointStr := "";
    for vertex in vertices do
        for i := 1 to #quotient`simplex[{vertex}]`cosets do
            rf := RealField(5);

            pointStr *:= Sprintf("\t\t\t\t\t<p name=\"%o%o\">%o</p>\n", 
                          makeSimplexName({vertex}), i,
                          Sprint(rf! coordinates[vertex][i][1]) * " " * 
                          Sprint(rf! coordinates[vertex][i][2])  * " " * 
                          Sprint(rf! coordinates[vertex][i][3]));
        end for;
    end for;    
    s *:= pointStr;

    s *:= "\t\t\t\t</points>
\t\t\t\t<colors type=\"rgb\">\n";

    for color in colors do
        s*:= "\t\t\t\t\t<c>" * color * "</c>\n";
    end for;

    s *:= "\t\t\t\t</colors>
\t\t\t</pointSet>
\t\t\t<faceSet face=\"show\" edge=\"hide\" color=\"show\">
\t\t\t\t<faces>\n";

    // output 2-simplices

    colors := [];
    //cosetColor := AssociativeArray();
    for simplex in Keys(quotient`simplex) do
        if #simplex ne 3 then
            continue;
        end if;
        for i := 1 to #quotient`simplex[simplex]`cosets do
            coset := Set(quotient`simplex[simplex]`cosets[i]);
            if coset notin Keys(cosetColor) then
                cosetColor[coset] := RandomColor();                
            end if;
            Append(~colors, cosetColor[coset]);

            vertexIndex := AssociativeArray();
            for edge in Subsets(simplex, 2) do
                indexEdge := quotient`simplex[simplex]`faces[edge][i];
                for vertex in edge do
                    indexVertex := quotient`simplex[edge]`faces[{vertex}][indexEdge];
                    vertexIndex[vertex] := indexVertex;
                end for;
            end for;
            s *:= "\t\t\t\t\t<f>";
            for vertex in Keys(vertexIndex) do
                s *:= Sprint(indices[vertex][vertexIndex[vertex]]) * " ";
            end for;
            s *:= "</f>\n";
        end for;
    end for;

    s *:= "\t\t\t\t</faces>
\t\t\t\t<colors type=\"rgb\">\n";

    for color in colors do
        s*:= "\t\t\t\t\t<c>" * color * "</c>\n";
    end for;

    s *:= "\t\t\t\t</colors>             
\t\t\t</faceSet>
\t\t</geometry>
\t\t<geometry>
\t\t\t<pointSet point=\"hide\" dim=\"3\">
\t\t\t\t<points>\n";

    s *:= pointStr;

    s *:= "\t\t\t\t</points>
\t\t\t</pointSet>     
\t\t\t<lineSet line=\"show\" color=\"show\">
\t\t\t\t<lines>
\t\t\t\t\t<thickness>4.0</thickness>";
    
    // output 1-simplices

    colors := [];
    //cosetColor := AssociativeArray();
    for simplex in Keys(quotient`simplex) do
        if #simplex ne 2 then
            continue;
        end if;
        for i := 1 to #quotient`simplex[simplex]`cosets do
            coset := Set(quotient`simplex[simplex]`cosets[i]);
            if coset notin Keys(cosetColor) then
                cosetColor[coset] := RandomColor();                
            end if;
            Append(~colors, cosetColor[coset]);    

            s *:= "\t\t\t\t\t<l>";
            for vertex in simplex do
                s *:= Sprint(indices[vertex][quotient`simplex[simplex]`faces[{vertex}][i]]) * " ";
            end for;
            s *:= "</l>\n";
        end for;
    end for;

    s *:= "\t\t\t\t</lines>
\t\t\t\t<colors type=\"rgb\">\n";

    for color in colors do
        s*:= "\t\t\t\t\t<c>" * color * "</c>\n";
    end for;    

    s *:= "\t\t\t\t</colors>
\t\t\t</lineSet>      
\t\t</geometry>
\t</geometries>
</jvx-model>\n";

    return s;
end intrinsic;