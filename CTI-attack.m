clear;

load "group-action.m";

// magma code for the minrank computation from https://arxiv.org/pdf/2002.08322
// and a computational attack on CTI variant from https://eprint.iacr.org/2023/723

// ----------------------- MIN RANK ---------------------------------------
// given a list L of n square t x t matrices, compute the lin. comb. of matrices whose rank is \leq r
// with current normalizing steps, we do not get all of the solutions every time
ComputeMinRank := function(L)
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

// ----------------------------- COMPUTATIONAL ATTACK (on CTI variant) ------------------------------------

// given a public key (tensor), L, find A,B,C such that (A,B,C) \star t_0 = L
CompAttack  := function(L)
	pts:=ComputeMinRank(L); // rank 1 points of L
	if #pts lt n then // sanity check that there are enough rank 1 points
		return "error: not enough rank 1 points.";
	end if;
	R<[X]> := PolynomialRing(F,2*n^2); // vars for B1 and C1-inv
	lst := [R!pts[i][j]:i,j in [1..n]]; //
	A := (Matrix(n,n,lst)); // A^-1 built using rank1 points
	I := identity(n,R); // make id matrix
	B := Matrix(n,n,[X[i]:i in [1..n^2]]); // build B using variables
	LHS := Commitment(I,B,I,0); // LHS = (I,B,I) \star t_0
	D := Matrix(n,n,[X[i]:i in [n^2+1..2*n^2]]); // build C^-1 using poly. ring variables
	RHS := star(A,I,D,L); // (A^inv,I,C^inv) star L
	// make equations for Grobner basis
	eqns := [LHS[i][j][k] - RHS[i][j][k]:i,j,k in [1..n]];
	norm_row := [X[i]-1:i in [1..n-1]];
	eqns := eqns cat [X[2*n^2-1]-1] cat norm_row; // normalize first row of B and one entry in C-inv
	I := Ideal(eqns); // solve equations
	sols := Variety(I: Al := "Wiedemann");
	return sols;
end function;

CheckCorrectness := function(sols,pts,L) // checks solutions for CompAttack();
	if #pts lt n then 
		"not enough rank 1 points";
		return false;
	end if;
	valid := 0;
	check := false;
	for s in [1..#sols] do 
		lst1:=[pts[i][j]:i,j in [1..n]]; // apply scalars found to A^-1
		A := (Matrix(n,n,lst1));
		B := Matrix(n,n,[sols[s][i]:i in [1..n^2]]); // build matrices from solution
		D := Matrix(n,n,[sols[s][i]:i in [n^2+1..2*n^2]]);
		// check that solutions correspond to invertible matrices
		if Determinant(A) ne 0 and Determinant(B) ne 0 and Determinant(D) ne 0 then
			C := D^-1;
			A1 := A^-1;
			L1 := Commitment(A1,B,C,0); // check correctness
			if L eq L1 then 
				valid +:=1;
				check := true;
			end if;
		end if;
	end for;
	return check;
end function;


A,B,C,b := keygen(); // compute sk
L := Commitment(A,B,C,0); // compute pk
pts := ComputeMinRank(L); // compute minrank to find rank1 points
if #pts eq n then // make sure there's enough rank1 points
	"attack time";
	time sols := CompAttack(L); // run attack
	"sols"; #sols;
	c := CheckCorrectness(sols,pts,L); // check correctness	
end if;
