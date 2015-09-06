/*
 * Copyright (c) 2015 Lutz Hofmann
 * Licensed under the MIT license, see LICENSE.txt for details.
 */

function LatexPrintMatrix(M)
	s := "\\begin{pmatrix} ";
	for i := 1 to NumberOfRows(M) do
		for j := 1 to NumberOfColumns(M) do
			s *:= Sprint(M[i,j]);
			if j lt NumberOfColumns(M) then
				s *:= " & ";
			end if;
		end for;
		if i lt NumberOfRows(M) then
			s *:= " \\\\ ";
		end if;
	end for;
	s *:= "\\end{pmatrix}";
	return s;
end function;

function LatexPolynomial(poly)
	poly := StringReplace(poly, "*", "");
	poly := StringReplace(poly, "^", "^{");

	i := 1;
	repeat
		if poly[i] eq "{" then
		    while (poly[i] ne " ") and (i ne #poly) do
		    	i +:= 1;
		    end while;
		    poly := Substring(poly, 1, i-1) * "}" * Substring(poly, i, #poly);
		end if;
		i +:= 1;
	until i ge #poly;

	return poly;
end function;

function LatexFactorization(x)
	factors := Factorization(x);
	s := "";
	for factor in factors do
		poly := LatexPolynomial(Sprint(factor[1]));

		s *:= "(" * poly * ")";		
		if factor[2] gt 1 then
			s *:= "^{" * Sprint(factor[2]) * "}";
		end if;
	end for;
	return s;
end function;
