n:=3;
F := FiniteField(11);

tensor_prod := function(u,v,w)
// return the tensor product of u,v,w of dim n as an n x n x n array 
//assume the input vectors are array of coefficients with respect to the canonical basis of F_q^n
	tsr := Matrix(F,n,1,v)*Transpose(Matrix(F,n,1,w)); //tested and works 
	tsr;
	lst:=[* *];
	for i in [1..n] do
		"u[i]:";
		u[i];
		"tsr:";
		tsr;
		mat:=ScalarMatrix(F,n,u[i]);
		el:= [* mat*tsr *]; // u_i multiplies each element of tsr
		"element is:";
		el;
		lst := lst cat el;
	end for;
	"final tensor product";
	lst;
	//output := tsr*Transpose(Matrix(F,n,1,w));
	return 0; //output;
end function;

u:=[1,2,3];
v:=[4,5,6];
w:=[7,8,9];

tensor_prod(u,v,w);
tsr1:=TensorProduct(Matrix(F,n,1,v),Matrix(F,n,1,w));
TensorProduct(tsr1,Matrix(F,n,1,u))
