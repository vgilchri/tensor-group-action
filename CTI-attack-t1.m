clear;

load "group-action.m";

// magma code for a variant of minrank from https://arxiv.org/pdf/2002.08322
// and a computational attack on CTI variant for t1 from https://eprint.iacr.org/2023/723

// ----------------------- MIN RANK ---------------------------------------
// given a list L of n square t x t matrices, compute the lin. comb. of matrices whose rank is \leq r
// with current normalizing steps, we do not get all of the solutions every time
// we add an extra normalizing step for our attack later on that normalizes the x^th component to 1
t1MinRank := function(L,x)
	r := 1; // we only care about having target rank 1

	// set up the instance of minrank -------------
	n := #L; // number of matrices and dim of each matrix
	F := Parent(L[1][1][1]); // determine base field
	P<[X]> := PolynomialRing(F,2*n); // create polynomial ring with variables x_i (=X[1..n]), but also the c_T (=X[n+1..n+t])

	M := ZeroMatrix(F,n); // create a matrix storing the desired lin. comb. in terms of the new variables, i.e. M = x1 M1 + ...xn Mn
	for i in [1..n] do 
		M := M + X[i]*L[i];
	end for;

	// compute equations to be solved using support minors --------
	eqns := []; // store here the equations we build
	for i in [1..n] do // for each row in M
		for j in [1..n-1] do // choose the first column
			for k in [j+1..n] do // choose the second column
				temp := M[i][j]*X[k+n] - M[i][k]*X[j+n]; // determinant should be zero
				eqns cat:= [temp];
			end for;
		end for;
	end for;
	eqns cat:= [X[x]-1]; // normalize the x^th component to 1
	norm_cofacs := [X[n+1]-1]; // normalize first entry of cofactor variables (skips the solutions with this value 0, so we consider later on)
	norm_pt := [X[n]-1]; // normalize last entry of rank 1 point (consider X[n]=0 later on)
	// solve the equations we've gathered
	I := Ideal(eqns cat norm_cofacs cat norm_pt);
	sol := Variety(I:Al := "KellerGehrig"); // Wiedemann won't work, so we use a similar algo instead
	points := sol; // the final result to return, but first check if it has all the solutions
	// check if not enough solutions, if so, consider new normalizing factors
	t := 1;
	norm_pt := [X[n],X[n-1]-1];
	while #points lt n and t lt n do 
		norm_pt := norm_pt[1..#norm_pt-1] cat [X[n-t+1],X[n-t]-1]; // remove previous normalizing factor and add new zero
		I := Ideal(eqns cat norm_cofacs cat norm_pt);
		sol := Variety(I:Al := "KellerGehrig");
		points cat:= sol;
		t +:= 1;
	end while;
	return points;
end function;

// ----------------------------- COMPUTATIONAL ATTACK (CTI for t_1) ------------------------------------


Rank0Point := function(pk) // find the rank 0 point
	poly<[AA]> := PolynomialRing(F, n); // define variables to be solved
	M := ZeroMatrix(F,n); // initialize matrix to store equations
	for i in [1..n] do 
		M := M + AA[i]*pk[i]; // compute set of equations: a1 G1 + ... an Gn
	end for;
	eqs := [M[i][j]:i,j in [1..n]] cat [AA[1]-1];
	point := Variety(Ideal(eqs)); // solve equations
	M := Matrix(1,n,[point[1][i]:i in [1..n]]);
	return M;
end function;

CompAttackt1 := function(L)
	P0 := Rank0Point(L); // find rank 0 point
	x := 1;
	while P0[1][x] eq 0 do // find first non-zero entry of rank 0 point
		x +:= 1;
	end while;
	pts := t1MinRank(L,x); // compute minrank to find rank1 points
	entries := [];
	for i in [1..n-1] do 
		entries cat:= [pts[i][j]: j in [1..n]]; // make matrix out of rank 1 points
	end for;
	entries cat:= [P0[1][i] : i in [1..n]]; // add rank 0 point as last column
	A := Matrix(n,n,entries); // A^-1
	R<[X]> := PolynomialRing(F,2*n^2); // vars for B and C 
	A3 := Matrix(R,A);
	I := identity(n,R); // make id matrix
	B := Matrix(n,n,[X[i]:i in [1..n^2]]); // build B using variables
	D := Matrix(n,n,[X[i]:i in [n^2+1..2*n^2]]); // build C using poly. ring variables
	LHS := Commitment(I,B,D,1); // LHS = (I,B,C) \star t_0
	RHS := star(A3,I,I,L); // (A^inv,I,I) star L
	// 	// make equations for Grobner basis
	eqns := [LHS[i][j][k] - RHS[i][j][k]:i,j,k in [1..n]];
	eqns cat:= [B[j][n] : j in [1..n]]; // last column can be anything, so fix it
	eqns cat:= [B[n][j]-1 : j in [1..n-1]]; // fix last row
	eqns cat:= [D[j][n] : j in [1..n]]; // fix last column of C
	I := Ideal(eqns); // solve equations
	sols := Variety(I);
	return sols;
end function;

I := identity(n,F);
A,B,C,b := keygen(); // compute sk
L := Commitment(A,B,C,1);// pk
time sol := CompAttackt1(L);



