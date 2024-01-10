clear;

load "rank0attack.m";

// magma code for the minrank computation from https://arxiv.org/pdf/2002.08322


//-------------------------------------------------


// given a list L of n square t x t matrices, compute the lin. comb. of matrices whose rank is leq r
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
				eqns := eqns cat [temp];
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
		r := 1;
		norm_cofacs := [1,X[n+1]-1];
		while #points lt n and r lt n do 
			I := Ideal(eqns cat norm_cofacs cat norm_pt);
			sol := Variety(I:Al := "KellerGehrig");
			points cat:= sol;
			norm_cofacs := norm_cofacs[1..#norm_cofacs-1] cat [X[n+r],X[n+r+1]-1]; // remove previous normalizing factor and add new zero
			r +:= 1;
		end while;
		I := Ideal(eqns cat norm_cofacs cat norm_pt);
		sol := Variety(I:Al := "KellerGehrig");
		points cat:= sol;
		I := Ideal(eqns cat norm_cofacs[1..#norm_cofacs-1] cat [X[2*n]] cat norm_pt);
		sol := Variety(I:Al := "KellerGehrig");
		points cat:= sol;
		t +:= 1;
	end while;
	return points;
end function;

// t is dim of square matrices, r is target minrank, F is base field
// generate random instance to input into minrank
MakeList := function(t,F) 
	// generate list of t x t matrices
	L := [];
	for i in [1..t] do 
		M := RandomMatrix(F,t,t);
		L := L cat [M];
	end for;
	return L;
end function;

// determine whether result from minrank gives a matrix of appropriate rank
CheckSol := function(sol, L)
//given a list of L matrixes and coeffs in sol check whether rank of sum(x_i)L_i is <=1 
	n := #L; // number of matrices
	t := #Rows(L[1]); // dim of matrices in L
	F := Parent(L[1][1][1]);
	sum:=ZeroMatrix(F,t,t);
		for i in [1..n] do
			sum:=sum+sol[i]*L[i];
		end for;
	return Rank(sum);
end function;

star := function(A,B,C,X)
// performs the general group action (A,B,C)*X
//Assume X is represented using our tensor product representation as above. 
sum:=0;
lst:=[**];
for l in [1..n] do
    mat:=identity(n,Parent(A[1][1]));
	//ei := Matrix(n,1,basis[i]);
        for m in [1..n] do
        //ej := Matrix(n,1,basis[j]);
            for r in [1..n] do
                sum:=0;
                for i in [1..n] do
                    el:=X[i];
                    for j in [1..n] do
                        for k in [1..n] do
                            coeff:=el[j][k]*A[l][i]*B[m][j]*C[r][k];
                            sum:=sum+coeff;
                        end for;
                    end for;
                end for;
            mat[m][r]:=sum;
            end for;
        end for;
    el:=[*mat*];
        //"matrix in a list";
       // el;
    lst:=lst cat el; 
end for;
return lst;      
end function;

// function to better name the variables of our polynomial ring in CompAttack()
NameVars := function()
	B := ["b_" cat IntegerToString(i) cat IntegerToString(j) : i,j in [1..n]];
	C := ["c_" cat IntegerToString(i) cat IntegerToString(j) : i,j in [1..n]];
	lams := ["lambda_" cat IntegerToString(i): i in [1..n]];
	vars := B cat C cat lams;
	return vars;
end function;

// given a public key (tensor) L, find A,B,C such that (A,B,C) star t_0 = L
CompAttack  := function(L)
	pts:=ComputeMinRank(L);
	if #pts lt n then // check there are enough rank 1 points
		return "error: not enough rank 1 points. try again.";
	end if;
	R<[X]> := PolynomialRing(F,2*n^2+n); // vars for B1 and C1-inv, but also the scalar factors acting on A
	vars := NameVars(); // rename the variables in the polynomial ring to make it easier to read when printing
	AssignNames(~R,vars);
	lst := [];
	for i in [1..n] do // with rank 1 points, build a matrix
		lst := lst cat [pts[i][j]*X[2*n^2+j]:j in [1..n]]; //
	end for;
	A := Transpose(Matrix(n,n,lst)); //
	//A := Matrix(n,n,lst);
	// (I,B1,I) star (A1,I,I) star t_0
	I1 := identity(n,R); // make id matrix
	f1 := Commitment(A,I1,I1,0);
	B1 := Matrix(n,n,[X[i]:i in [1..n^2]]);
	LHS := star(I1,B1,I1,f1);
	//LHS := Commitment(A1,B1,I1,0);
	// (I,I,C1^inv) star L
	D1 := Matrix(n,n,[X[i]:i in [n^2+1..2*n^2]]);
	RHS := star(I1,I1,D1,L);
	// solve vars
	eqns := [];
	for i in [1..n] do // make equations by subtracting tensors
		for j in [1..n] do 
			for k in [1..n] do 
				eqns := eqns cat [LHS[i][j][k] - RHS[i][j][k]];
			end for;
		end for;
	end for;
	lam_prod := 1;
	for i in [1..n] do 
		lam_prod *:= X[2*n^2+i]; // product of all the scaling factors of A
	end for;
	eqns := eqns cat [lam_prod-1];
	I := Ideal(eqns); // solve equations (should be linear) with Groebner basis
	sols := Variety(I);
	return sols;
end function;

CheckAllSols := function(sols,pts,L) // checks solutions for CompAttack();
	if #pts lt n then 
		"not enough rank 1 points";
		return false;
	end if;
	for s in [1..#sols] do 
		lst1:=[pts[i][j]*sols[s][2*n^2+j]:i,j in [1..n]]; // apply scalars found to A
		A := Transpose(Matrix(n,n,lst1));
		B := Matrix(n,n,[sols[s][i]:i in [1..n^2]]);
		C := Matrix(n,n,[sols[s][i]:i in [n^2+1..2*n^2]]);
		if Determinant(A) ne 0 and Determinant(B) ne 0 and Determinant(C) ne 0 then
			D := C^-1;
			L1 := Commitment(A,B,D,0);
			if L eq L1 then 
				return true;
			end if;
		end if;
	end for;
	return false;
end function;



I := identity(n,GF(q));
t0 := Commitment(I,I,I,0);
ComputeMinRank(t0);




//T := 0;
//F := 0;
//for i in [1..100] do 
//	A,B,C,b := keygen();
//	L := Commitment(A,B,C,0); // compute pk
//	sols := CompAttack(L); // compute attack
//	pts := ComputeMinRank(L); // compute minrank for checking
//	#pts;
//	if #pts gt n-1 then // if enough rank 1 points for attack
//		c := CheckAllSols(sols,pts,L); // check if any of recovered solutions work
//		if c eq true then 
//			T +:= 1;
//		else 
//			F +:=1;
//		end if;
//	end if;
//end for;
//"true: "; T; "false: "; F;


