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
	vars := B cat C;
	return vars;
end function;

// given a public key (tensor), L, and rank1 points of L, pts, find A,B,C such that (A,B,C) star t_0 = L
CompAttack  := function(L,pts)
	//pts:=ComputeMinRank(L);
	if #pts lt n then // check there are enough rank 1 points
		return "error: not enough rank 1 points. try again.";
	end if;
	R<[X]> := PolynomialRing(F,2*n^2); // vars for B1 and C1-inv
	// vars := NameVars(); // rename the variables in the polynomial ring to make it easier to read when printing
	// AssignNames(~R,vars);
	lst := [R!pts[i][j]:i,j in [1..n]]; //
	A := (Matrix(n,n,lst)); // A^-1 built using rank1 points
	I := identity(n,R); // make id matrix
	B := Matrix(n,n,[X[i]:i in [1..n^2]]); // build B using variables
	LHS := Commitment(I,B,I,0); // LHS = (I,B,I) \star t_0
	D := Matrix(n,n,[X[i]:i in [n^2+1..2*n^2]]); // C^-1
	RHS := star(A,I,D,L); // (A^inv,I,C^inv) star L
	// make equations for Grobner basis
	eqns := [LHS[i][j][k] - RHS[i][j][k]:i,j,k in [1..n]];
	eqns cat:= [Determinant(D)-1,X[1]-1]; // normalize determinant of D, and first entry of B
	I := Ideal(eqns); // solve equations with Groebner basis
	sols := Variety(I: Al := "Wiedemann");
	return sols;
end function;

CompAttack2  := function(L,pts)
	//pts:=ComputeMinRank(L);
	if #pts lt n then // check there are enough rank 1 points
		return "error: not enough rank 1 points. try again.";
	end if;
	R<[X]> := PolynomialRing(F,2*n^2); // vars for B1 and C1-inv
	// vars := NameVars(); // rename the variables in the polynomial ring to make it easier to read when printing
	// AssignNames(~R,vars);
	lst := [R!pts[i][j]:i,j in [1..n]]; //
	A := (Matrix(n,n,lst)); // A^-1 built using rank1 points
	I := identity(n,R); // make id matrix
	B := Matrix(n,n,[X[i]:i in [1..n^2]]); // build B using variables
	LHS := Commitment(I,B,I,0); // LHS = (I,B,I) \star t_0
	D := Matrix(n,n,[X[i]:i in [n^2+1..2*n^2]]); // C^-1
	RHS := star(A,I,D,L); // (A^inv,I,C^inv) star L
	// make equations for Grobner basis
	eqns := [LHS[i][j][k] - RHS[i][j][k]:i,j,k in [1..n]];
	lst := [];
	for i in [1..n^3] do 
		terms := [];
		for j in [1..2*n^2] do 
			coef := Coefficients(eqns[i],j);
			if #coef eq 1 then 
				terms cat:= [R!0];
			else
				terms cat:= [R!coef[2]];
			end if;
		end for;
		lst cat:= terms;
	end for;
	M := Matrix(n^3,2*n^2,lst);
	sols := Kernel(M);
	return sols;
end function;

CheckAllSols := function(sols,pts,L) // checks solutions for CompAttack();
	if #pts lt n then 
		"not enough rank 1 points";
		return false;
	end if;
	for s in [1..#sols] do 
		lst1:=[pts[i][j]:i,j in [1..n]]; // apply scalars found to A^-1
		A := (Matrix(n,n,lst1));
		B := Matrix(n,n,[sols[s][i]:i in [1..n^2]]); // build matrices from solution
		D := Matrix(n,n,[sols[s][i]:i in [n^2+1..2*n^2]]);
		// most solutions do not correspond to invertible matrices
		if Determinant(A) ne 0 and Determinant(B) ne 0 and Determinant(D) ne 0 then
			C := D^-1;
			A1 := A^-1;
			L1 := Commitment(A1,B,C,0); // check correctness
			if L eq L1 then 
				return true;
			end if;
		end if;
	end for;
	return false;
end function;


I := identity(n,GF(q));
check := true;
for i in [1..1] do 
	A,B,C,b := keygen();
	L := Commitment(A,B,C,0); // compute pk
	pts := ComputeMinRank(L); // compute minrank to find rank1 points
	if #pts eq n then 
		time sols := CompAttack(L,pts);
		#sols;
		check := check and CheckAllSols(sols,pts,L);
	else
		"error : not enough rank1 points to run attack";
	end if;
end for;
check;
