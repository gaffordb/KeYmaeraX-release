(* ::Package:: *)

BeginPackage[ "Boreale`"]


Post::usage="Post"
PostUnsound::usage="PostUnsound"


Begin[ "Private`" ]


(* Computing the maximal total polynomial degree of a given polynomial P *)
PolynomDegree[P_]:=Module[{}, Max[Map[Apply[Plus, #]&,Map[#[[1]]&,CoefficientRules[P]]]] ]


(* Given a polynomial p, check that p is in the ideal <generators> *)
IsInIdeal[p_,generators_List,vars_List,parameters_List]:=Module[{GB, rem},
GB = GroebnerBasis[generators, Join[parameters,vars], MonomialOrder->Lexicographic];
rem = PolynomialReduce[p, GB, Join[parameters,vars], MonomialOrder->Lexicographic][[2]];
TrueQ[rem==0]
]


(* Formal Lie derivative computation *)
LieD[p_,vars_List,vectorField_List]:=Module[{},Expand[Grad[p,vars].vectorField]]


(* Computing the solution to the linear set of constraints on symbolic remainder coefficients *)
ComputeV[remainders_List,templateCoeffs_List,vars_List]:=Module[{eqZero,coeffs,sol},
coeffs=DeleteDuplicates[Flatten[CoefficientList[remainders,vars]]];
eqZero=Map[#==0&, coeffs];
sol=Solve[eqZero,templateCoeffs]//First
]


(* Boreale method for computing polynomial invariants *)
Post[pre_List,deg_Integer?NonNegative,vars_List,vectorField_List]:=Catch[Module[{
preGB,MonBas,TemplateCoeffs,PTemplate,LfPTemplate,problem,sol,Dbxs,rem,V,J,pi,m,rk,finalSol,res,rems,idealSaturation,resultTemplate,

(* PREPORCESSING *)
(* Maximum total polynomial degree of the vector field *)
d=Max[Map[PolynomDegree,vectorField]]},
(* Find the Groebner basis for the ideal generated by the algebraic precondition *)
preGB=GroebnerBasis[pre,vars];
(* Compute the monomial basis *)
MonBas=FromCoefficientRules[CoefficientRules[(Apply[Plus, vars]+1)^deg, vars]/.{Rule[exp_,coeff_]:>Rule[exp,1]}, vars]//MonomialList;
(* Create a template polynomial with symbolic coefficients *)
TemplateCoeffs=Table[Symbol["COEFF"<>ToString[i]], {i,1,Length[MonBas]}]//Reverse;

(* INITIALISATION *)
pi={Evaluate[TemplateCoeffs.MonBas]}; (* initialise list with only with \[Pi]^(0), i.e. the symbolic polynomial template *)
rems={PolynomialReduce[pi//Last,preGB,Join[TemplateCoeffs,vars]]//Last}; (* initialise list of remainders with \[Pi]^(0) mod GB of the precondition *)
V[0]=ComputeV[rems,TemplateCoeffs,vars]; (* compute the initial solution set, corresponding to the vector space Subscript[V, 0] *)
J[0]=pi/.V[0]; (* \[Pi]^(0)(Subscript[V, 0]) *)
rk[0]=1; (* set the initial rank of initial dimension of the vector space to 1 *)

Do[ (* MAIN LOOP *)
(* V(i) is the set of solutions to rem(0)\[Equal]rem(1)\[Equal] ... ==rem(i)==0  *)
pi=pi~Join~{LieD[Last[pi],vars,vectorField]};
rems=rems~Join~{PolynomialReduce[pi//Last,preGB,Join[TemplateCoeffs,vars]]//Last};
(*Print[pi//MatrixForm];
Print[rems//MatrixForm];*)
V[i]=ComputeV[rems,TemplateCoeffs,vars];
(*Print[V[i]];*)
J[i]=pi/.V[i];
(*Print[J[i]//MatrixForm];
Print["Is in ideal?"]; *)
rk[i]=MatrixRank[Table[TemplateCoeffs/.V[j], {j,0,i}]//Transpose];
(* Only compute GB if the vector space rank has saturated *)
idealSaturation=If[TrueQ[rk[i]==rk[i-1]], IsInIdeal[(pi//Last)/.V[i], J[i-1],vars,TemplateCoeffs], False];
resultTemplate=(TemplateCoeffs.MonBas)/.V[i];
If[TrueQ[rk[i]==rk[i-1] && idealSaturation], 
Print["Done!"];
Throw[Select[DeleteDuplicates[Grad[resultTemplate, TemplateCoeffs]//Flatten], Not[NumericQ[#]]&]]
], {i,1,Infinity}];
]]


(* Boreale method for computing polynomial invariants *)
PostUnsound[pre_List,deg_Integer?NonNegative,vars_List,vectorField_List]:=Catch[Module[{
preGB,MonBas,TemplateCoeffs,PTemplate,LfPTemplate,problem,sol,Dbxs,rem,V,J,pi,m,rk,finalSol,res,rems,idealSaturation,resultTemplate,

(* PREPORCESSING *)
(* Maximum total polynomial degree of the vector field *)
d=Max[Map[PolynomDegree,vectorField]]},
(* Find the Groebner basis for the ideal generated by the algebraic precondition *)
preGB=GroebnerBasis[pre,vars];
(* Compute the monomial basis *)
MonBas=FromCoefficientRules[CoefficientRules[(Apply[Plus, vars]+1)^deg, vars]/.{Rule[exp_,coeff_]:>Rule[exp,1]}, vars]//MonomialList;
(* Create a template polynomial with symbolic coefficients *)
TemplateCoeffs=Table[Symbol["COEFF"<>ToString[i]], {i,1,Length[MonBas]}]//Reverse;

(* INITIALISATION *)
pi={Evaluate[TemplateCoeffs.MonBas]}; (* initialise list with only with \[Pi]^(0), i.e. the symbolic polynomial template *)
rems={PolynomialReduce[pi//Last,preGB,Join[TemplateCoeffs,vars]]//Last}; (* initialise list of remainders with \[Pi]^(0) mod GB of the precondition *)
V[0]=ComputeV[rems,TemplateCoeffs,vars]; (* compute the initial solution set, corresponding to the vector space Subscript[V, 0] *)
J[0]=pi/.V[0]; (* \[Pi]^(0)(Subscript[V, 0]) *)
rk[0]=1; (* set the initial rank of initial dimension of the vector space to 1 *)

Do[ (* MAIN LOOP *)
(* V(i) is the set of solutions to rem(0)\[Equal]rem(1)\[Equal] ... ==rem(i)==0  *)
pi=pi~Join~{LieD[Last[pi],vars,vectorField]};
rems=rems~Join~{PolynomialReduce[pi//Last,preGB,Join[TemplateCoeffs,vars]]//Last};
(*Print[pi//MatrixForm];
Print[rems//MatrixForm];*)
V[i]=ComputeV[rems,TemplateCoeffs,vars];
(*Print[V[i]];*)
J[i]=pi/.V[i];
(*Print[J[i]//MatrixForm];
Print["Is in ideal?"]; *)
rk[i]=MatrixRank[Table[TemplateCoeffs/.V[j], {j,0,i}]//Transpose];
resultTemplate=(TemplateCoeffs.MonBas)/.V[i];
If[TrueQ[rk[i]==rk[i-1]], 
Print["Done!"];
Throw[Select[DeleteDuplicates[Grad[resultTemplate, TemplateCoeffs]//Flatten], Not[NumericQ[#]]&]]
], {i,1,10}];
]]


End[]


EndPackage[]
