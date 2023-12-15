clear;

// magma code for the minrank computation from https://arxiv.org/pdf/2002.08322

// given a matrix,M, and a target rank, r, create the alg equations from support minors
BuildSupportMinors := function(M,r)

end function;

// given a list L of n square t x t matrices, compute the lin. comb. of matrices whose rank is leq r
ComputeMinRank := function(L)
	r := 1; // we only care about having target rank 1

	// set up the instance of minrank -------------
	n := #L; // number of matrices
	t := #Rows(L[1]); // dim of matrices in L
	F := Parent(L[1][1][1]); // determine base field
	P<[X]> := PolynomialRing(F,n+t); // create polynomial ring with variables x_i, but also the c_T
									 // x_i will be first n vars, and the c_T will be the remaining t of them
	M := ZeroMatrix(F,t); // create a matrix storing the desired lin. comb. in terms of the new variables, i.e. x1 M1 + ...xn Mn
	for i in [1..n] do 
		M := M + X[i]*L[i];
	end for;

	// compute equations to be solved using support minors --------
	eqns := []; // store here the equations we build
	for i in [1..t] do // for each row in M
		temp := 0;
		for j in [1..t] do // for each element in that row
			temp := temp + M[i][j]*X[j+n]*(-1)^(j); // determinant should be zero
			eqns := eqns cat [temp];
		end for;
	end for;
	eqns := eqns cat [X[n]-1]; // force last coordinate to be 1
	// solve the equations we've gathered
	I := Ideal(eqns);
	sol := Variety(I);
	return sol;
end function;

// t is dim of square matrices, r is target minrank, F is base field
MakeList := function(t,F) 
	// generate list of t x t matrices
	L := [];
	for i in [1..t] do 
		M := RandomMatrix(F,t,t);
		L := L cat [M];
	end for;
	return L;
end function;

L := MakeList(2,GF(5));
L;
ComputeMinRank(L,1);

