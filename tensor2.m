clear; 

n:= 3;
q := 5;
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
	A := Matrix(n,[X[i]:i in [1..n^2]]); // fill the matrices with our unknown variables
	B := Matrix(n,[X[i]:i in [(n^2 + 1)..(2*n^2)]]);
	C := Matrix(n,[X[i]:i in [(2*n^2 + 1)..(3*n^2)]]);
	I := identity(n,P); // make identity matrix
	LHS := GACE(A,B,I,b); // create the equations from Christophe's email
	RHS := fake_comp; // for now we use secret knowledge to compute the group action, should fix later
	ideal :=[]; // we will build an ideal with all the equations we want to solve
	for s in [1..n^3] do // make a list of all the equations
		eqn := LHS[s][1] - RHS[s][1];
		ideal := Append(ideal,eqn);
		if s le vars_num then 
			ideal := Append(ideal,X[s]^q-X[s]); // include field equations
		end if;
	end for;
 	// // add constraint on leaving t_b invariant - gets number of solutions down to zero lol :
	//eqn:=0;
	//for i in [1..n] do
	//for j in [1..n] do
	    //for k in [1..n] do  
	        //for s in [1..n] do
	            //eqn:=eqn +A[i][s]*B[j][s]*C[k][s]; //should it be C here ? or D ? might have to get a right implementation of fakecomp before being able to implement that properly.
	       //end for;
		// //if all indexes are equal sum must be 1 o.w. it is 0 
        	//if (i eq j) and (j eq k) then 
           		// eqn:=eqn-1;
        		//end if;
	    //eqn;
	    //ideal:=Append(ideal,eqn-1);
	    //end for;
	    //end for;
	    //end for;
	if Xgcd(n,q-1) eq 1 then // this only works if/when there are n^th roots
		ideal := Append(ideal,Determinant(A) - 1); // we add equations to ensure Determinant(A) = 1, same for C
		ideal := Append(ideal,Determinant(C) - 1); // (we do this in order to normalize / avoid multiplication by a scalar)
	else // if there aren't n^th roots, we have to use one of each coset representative to guess determinant
		"no n^th roots, need to add coset reps";
	end if; // this only works if/when there are n^th roots

	H := Ideal(ideal); // make the equations into an ideal
	solns := Variety(H); // solve the equations using built-in Magma functions
	return solns;
end function;


check_inv:=function(M,n,b)
//potential invariant matrix M 
I:=identity(n,P);
t_b:=GACE(I,I,I,b);
"t_b";
t_b;
inv:= GACE(M,M,M,b); // this is not equal to t_b :/ 
"inv";
inv;
return inv eq t_b;
end function;


//Some reality checks for invariance 
M:=Matrix(2,2,[P!0,P!1,P!1,P!0]);
"check invariance";
check_inv(M,n,0); // this is equal to t_b only when b=0 -> does it make sense ?


A,B,C,b,pk := keygen();
D := Matrix(n,[X[i]:i in [(2*n^2 + 1)..(3*n^2)]]);
fake_comp := GACE(A,B,D*C,b); // public key times variables we are looking for in C
//"solutions";
S := GrobnerAttack(pk,b,fake_comp); // for now we assume the correct commitment
// need to check later what happens when using the wrong commitment
"public key matrices:";
A; B; C;
"size of solution set:";
#S;
//"solution set:";
//S;

// Open questions:
// -> why always same number of solutions? Maybe example too small?
// -> why can we scale the determinants of the matrices? 
// 		- in the 2x2 case, I was looking at which solution corresponds to the pk
//		  and i don't get why we can scale the determinant. Say we are working 
//		  in F_3, and the determinant of A is 2. Here, to get the determinant of
// 		  A to be 1, we need to multiply A by the square root of 2, but 2 has no
// 		  square roots mod 3.

