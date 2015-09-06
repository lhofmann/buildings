/*
 * Copyright (c) 2015 Lutz Hofmann
 * Licensed under the MIT license, see LICENSE.txt for details.
 */

AttachSpec("lib/buildings.spec");
SetAssertions(1);
SetVerbose("buildingLib", true);
SetVerbose("buildingQuotient", true);
SetVerbose("harmonicCochains", true);

// set true for profiling
PROFILE := false;
if PROFILE then
    SetProfile(true);
end if;

// paths
GRAPHVIZ_DOT_PATH := "\"C:\\Program Files (x86)\\Graphviz2.38\\bin\\dot.exe\"";
JAVAVIEW_PATH := "..\\JavaView\\bin\\javaview.bat";
OUTPUT_DIR := "output/";

RUN_GRAPHVIZ := true;       // generate graph image file using graphviz
RUN_GRAPHVIZ_OPEN := true;  // open image file after it is created
RUN_JAVAVIEW := true;       // generate javaview file
RUN_JAVAVIEW_OPEN := true;  // open javaview file after it is created
USE_PYTHON := false;        // use python to compute javaview model (see graphlayout.py)

ADDITIONAL_LEVELS := 2;

// parameters for quotient building
d := 2;
q := 2;
K := GF(q);
R<T> := PolynomialRing(K);
N := T^2 + T + 1;


time quotient := QuotientGamma0N(d, N : additionalLevels := ADDITIONAL_LEVELS);

nonSimplicialData := QuotientNonSimplicialData(quotient);
if #nonSimplicialData eq 0 then
    print "Quotient is simplicial.";
else
    print "Non-simplicial gluing data: ", nonSimplicialData;
end if;

filePrefix := Sprintf("QUOTIENT_D~%o_Q~%o_N~%o_LEVELS~%o_", d, q, R ! N, ADDITIONAL_LEVELS);
filePrefix := StringReplace(filePrefix, " ", "");
filePrefix := StringReplace(filePrefix, "^", ".");

filename := OUTPUT_DIR * filePrefix * "deltaComplex.sage";
WriteBinary(filename, BinaryString(QuotientToDeltaComplex(quotient)) : Overwrite := true);

if RUN_GRAPHVIZ then
    tempFile := Tempname("temp/dotGraph.");
    WriteBinary(tempFile * ".dot", BinaryString(QuotientToDotGraph(quotient)) : Overwrite := true);
    filename := OUTPUT_DIR * filePrefix * "graph.png";        
    System(GRAPHVIZ_DOT_PATH * " -Tpng " * tempFile * ".dot -o " * filename);
    if RUN_GRAPHVIZ_OPEN then
        System("start " * filename);
    end if;
end if;

if RUN_JAVAVIEW and (d in [1,2,3]) then
    filename := OUTPUT_DIR * filePrefix * "javaview.jvx";
    WriteBinary(filename, BinaryString(QuotientToJavaView(quotient : OptimizationSteps := 100, Python := USE_PYTHON)) : Overwrite := true);
    
    if RUN_JAVAVIEW_OPEN then
        System(JAVAVIEW_PATH * " " * filename);
    end if;
end if;

if PROFILE then
    SetProfile(false);
    profile := [Label(v) : v in V where V is Vertices(ProfileGraph())];
    Sort(~profile, func<x,y| y`Time - x`Time>);
    profile;
end if;
