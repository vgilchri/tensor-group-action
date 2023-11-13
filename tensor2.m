clear; 

n:= 2;
q := 41;
F := FiniteField(q);
vars_num := 3*n^2; // can put this later in attack function
P<[X]>:=PolynomialRing(F,vars_num); // define a polynomial ring for unknown values
gens := <X[i] : i in [1..vars_num]>; // name all the variables we need to solve for


identity := function(k,FF)
// makes k x k identity matrix
	basis := []; // compute basis vectors
	for i in [1..k] do 
		e := [FF!0 : j in [1..k]];
		e[i] := FF!1;
		basis := basis cat e;
	end for;
	M := Matrix(k,basis);
	return M;
end function;

IsInvertible := function(M)
	Z := Parent(M[1][1]);
	det := Determinant(M);
	det := Z!det;
	if det eq 0 then 
		return false;
	end if;
	return true;
end function;

InvMatrix := function(n)
	A := Matrix(n,n,[P!Random(F):i in [1..n^2]]);
	while IsInvertible(A) eq false do 
		A := Matrix(n,n,[P!Random(F):i in [1..n^2]]);
	end while;
	return A;
end function;

GACE := function(A,B,C,b)
// input: n x n matrices A,B,C and a bit b
// output: a sum of tensors relying on the input
	basis := identity(n,P);
	max := n-b; // the bit determines whether to include the last tensor or not
	sum := 0; // compute actual group action: a sum of tensors
	for k in [1..max] do 
		ei := Matrix(n,1,basis[k]); // make the basis vectors matrix type
		termA := A*ei;
		termB := B*ei;
		termC := C*ei;
		tensor1 := TensorProduct(termA,termB);
		tensor2 := TensorProduct(tensor1,termC);
		if sum eq 0 then
			sum := tensor2;
		else 
			sum := sum + tensor2;
		end if;
	end for;
	return sum;
end function;

JouxAction := function(A,B,C) // updated version that matches with GACE
	basis:=identity(n,P);
	sum:=0;
	for s in [1..n] do
		for i in [1..n] do
		ei := Matrix(n,1,basis[i]);
			for j in [1..n] do
			ej := Matrix(n,1,basis[j]);
				for k in [1..n] do
				ek := Matrix(n,1,basis[k]);
				coeff:=A[i][s]*B[j][s]*C[k][s];
				tsr1 := TensorProduct(ei,ej);
				tsr2 := TensorProduct(tsr1,ek);
				term := coeff*tsr2;
				if sum eq 0 then 
					sum:= term; 
				else 
					sum:= sum + term;
				end if;
				end for;
			end for;
		end for;
	end for;
	return sum; 
end function;

star := function(A,B,C,elt)
// performs the general group action on two inputs
// not sure how this is done in the real world
// but the paper assumes it can be done, so we will assume the same
// !!!!!!!!!!!!! for now we assume the structure of the GACE but this should be generalized later !!!!!!!!!!!!!!!!!!!!!!
	action := GACE(A,B,C,1); // compute \Sigma A*e_i \otimes B*e_i \otimes C_e_i
	for i in [1..n^3] do 
		action[i] := action[i]*elt[i]; // scalar multiply relevant coefficients from input class group
	end for;
	return action;
end function;

keygen := function()
// chooses random secret key values, and computes the corresponding public key
	//b := Random(1);
	b := 0;
	A := InvMatrix(n);
	B := InvMatrix(n);
	C := InvMatrix(n);
	pk := GACE(A,B,C,b);
	return A,B,C,b,pk;
end function;

GrobnerAttack := function(pk,b,fake_comp)
// given an instance of GACE, we will determine one or two possible secret keys
// we use the public key, and its known structure, to set up a system of equations to be solved
// we then solve it using Grobner
	A := Matrix(n,[X[i]:i in [1..n^2]]); // fill the matrices with our unknowns
	B := Matrix(n,[X[i]:i in [(n^2 + 1)..(2*n^2)]]);

	I := identity(n,P); // make identity matrix
	LHS := GACE(A,B,I,b);
	RHS := fake_comp;//star(I,I,C,pk);
	ideal :=[]; // we will build an ideal with all the equations we want to solve
	for s in [1..n^3] do 
		eqn := LHS[s][1] - RHS[s][1];
		ideal := Append(ideal,eqn);
		ideal := Append(ideal,X[s]^2-X[s]);
	end for;
	// which monomial ordering should we be using?
	H := Ideal(ideal);
	solns := Variety(H); // solve the equations using a Gröbner basis
	#solns; 
	return solns;
end function;


A,B,C,b,pk := keygen();
D := Matrix(n,[X[i]:i in [(2*n^2 + 1)..(3*n^2)]]);
fake_comp := GACE(A,B,D*C,b); // public key times variables we are looking for in C
//"solutions";
B := GrobnerAttack(pk,b,fake_comp); // for now we assume the correct commitment
// need to check later what happens when using the wrong commitment

InLattice := function(B,pk) // checks if pk is in the lattice spanned by the tuples in B
// currently doesn't work, we get the error "ring is not a subring of the real field"
	sequence := [];
	for i in [2..#B] do // make solution space into matrix, then into lattice to check if pk is in it
		for j in [1..#B[i]] do 
			sequence := sequence cat [F!B[i][j]];
		end for;
	end for;
	M := Matrix(3*n^2,#B-1,sequence);
	L := LatticeWithBasis(M);
	p := [F!pk[i][1] : i in [1..n^3]]; // convert public key into a vector in the same parent as the lattice
	return p in L;
end function; 