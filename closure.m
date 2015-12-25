
(* experimental code for computing the integral closure of an algebra C(x)[D]/<L> *)
(* by M. Kauers, Dec 2014, based on theory developed together with C. Koutschan *)

If[ !NameQ["Der"], << HolonomicFunctions.m ]

Off[Solve::svars];

(*** we work with truncated formal series Sum[ a[i,j] x^(alpha+j)*Log[x]^i, {i,0,d},{j,0,Infinity}]. they are represented as lists of terms, with each term a[i,j] x^(alpha+j) Log[x]^i represented by {a[i,j], Term[alpha+j, i]}. ***)

(**
 INPUT:
   sol... a truncated series solution as list of terms
 OUTPUT:
   the corresponding mma expression
 EXAMPLE:
   In[154]:= SeriesSolutionToExpression[{{2,{3,4}},{5,{6,7}}}]
   Out[154]= 2*x^3*Log[x]^4 + 5*x^6*Log[x]^7
   In[155]:= SeriesSolutionToExpression[{{2,{3,4}},{5,{6,7}}}, Sqrt[2]]
   Out[155]=  2*(-Sqrt[2] + x)^3*Log[-Sqrt[2] + x]^4 + 5*(-Sqrt[2] + x)^6*Log[-Sqrt[2] + x]^7
 **)
SeriesSolutionToExpression[sol_, alpha_:0] :=
  Plus@@(sol /. {c_, Term[i_,j_]} -> c*(x-alpha)^i Log[x-alpha]^j) /. Sentinel[__] -> 0

(**
 INPUT:
   expr... an expression for a truncated series solution.
 OUTPUT:
   the corresponding list-of-terms representation (without sentinels)
 EXAMPLES: 
   In[186]:= SeriesSolutionFromExpression[x^(1/2) + 5 x^(3/2) - 7 x^(5/2)]
   Out[186]= {{1, {1/2, 0}}, {5, {3/2, 0}}, {-7, {5/2, 0}}}
   In[195]:= SeriesSolutionFromExpression[99 Log[x]^3]
   Out[195]= {{99, {0, 3}}}
 **)
SeriesSolutionFromExpression[expr_, alpha_:0] :=
  If[ alpha != 0, SeriesSolutionFromExpression[expr /. x -> x + alpha, 0],
    Module[ {exp, logx},
      exp = Flatten[Outer[List, Exponent[expr /. Log[x] -> logx, x, List], Exponent[expr /. Log[x] -> logx, logx, List]], 1];
      DeleteCases[Table[{Coefficient[Coefficient[expr, Log[x], exp[[i,2]]], x, exp[[i, 1]]], Term@@exp[[i]]}, {i, 1, Length[exp]}], {0,__}]      
    ]
  ]

(**
 INPUT:
   L... an element of OreAlgebra[Der[x]]
   alpha... an AlgebraicNumber object or a rational number
 OUTPUT:
   L(x+alpha,Der[x]) --- an operator whose solutions at x=0 agree with the solutions of L at x=alpha.
 **)
ChangeOfVariables[L_, alpha_:0] :=
  ToOrePolynomial[Normal[L] /. Der[x] -> D /. x -> x + alpha /. D -> Der[x], OreAlgebra[Der[x]]]

(**
 INPUT:
   L... an element of OreAlgebra[Der[x]]
   sol... a series solution in list-of-terms representation
   alpha... expansion point of the series solutions. 
 OUTPUT:
   the series obtained by applying L to sol, in list-of-terms representation
 EXAMPLES:
   In[314]:= SeriesSolutionApply[ToOrePolynomial[Der[x]-1], {{1,{3,4}}}]
   Out[314]= {{4, {2, 3}}, {3, {2, 4}}, {-1, {3, 4}}}
 **)
SeriesSolutionApply[L_, sol_, alpha_:0] :=
  Module[ {M, e, b},
    If[ alpha != 0, Return[SeriesSolutionApply[ChangeOfVariables[L, alpha], sol, 0]]];
    b = Max[Cases[sol, Sentinel[e_, _] -> e, Infinity]] - 1 - Min[0, Cases[sol, Term[e_,_] -> e, Infinity]];
    M = Normal[If[ NumberQ[b], Series[Normal[L] /. Der[x] -> D, {x,0,Ceiling[b]}] /. {D -> Der[x]}, L]];
    e = If[ M===0, 0, ValuationCorrection[M] - Exponent[M, Der[x]]];
    DeleteCases[Join[SeriesSolutionFromExpression[
      ApplyOreOperator[ToOrePolynomial[M, OreAlgebra[Der[x]]], SeriesSolutionToExpression[sol]]],
      Cases[sol, Sentinel[u_, v_] -> Sentinel[u+e,v]]],
      {_, Term[u_, _]} /; u > b+e]
  ];

(**
 INPUT:
   L.. an element of OreAlgebra[Der[x]]
   alpha... an AlgebraicNumber object or a rational number
 OUTPUT:
   the largest integer e such that (x-alpha)^e | (x-alpha)^(r-qq)*L((x-alpha)^qq)
 **)
ValuationCorrection[L_, alpha_:0] := 
   Module[ {r},
     r = Exponent[L, Der[x]];
     Min[Table[Exponent[Coefficient[L, Der[x], i] /. x -> x + alpha, x, Min] + r - i, {i, 0, r}]]
   ];

(**
 INPUT:
   L... an element of OreAlgebra[Der[x]]
   alpha... an AlgebraicNumber object (or a rational number)
   n... an integer
 OUTPUT:
   the first n terms of all the series solutions of L in (x-alpha)
   including logs. The number of terms returned is n + m where
   m is the maximum integer distance among any discinct roots of
   the characteristic polynomial. Results are in list-of-terms 
   representation.
 EXAMPLES:
   In[530]:= SeriesSolutionBasis[Annihilator[Exp[x]+Sqrt[1-x]][[1]], 0, 3]
   Out[530]= {{{1, {0, 0}}, {1/12, {2, 0}}, {1/72, {3, 0}}, {-7/576, {4, 0}}, 
     Sentinel[5, 0], Sentinel[5, 1]}, {{1, {1, 0}}, {5/12, {2, 0}}, {11/72, {3, 0}}, 
     {31/576, {4, 0}}, Sentinel[5, 0], Sentinel[5, 1]}}
   In[531]:= SeriesSolutionBasis[Annihilator[Exp[x]+Sqrt[1-x]][[1]], 1, 3] 
   Out[531]= {{{1, {0, 0}}, {1, {1, 0}}, {1/2, {2, 0}}, {1/6, {3, 0}}, Sentinel[4, 0]}, 
     {{1, {1/2, 0}}, Sentinel[9/2, 0]}}
   In[543]:= SeriesSolutionBasis[Annihilator[1/Sqrt[x-1]+1/(x^2-1), Der[x]][[1]], ToNumberField[Sqrt[2]], 2] 
   Out[543]= {{{1, {0, 0}}, {AlgebraicNumber[Sqrt[2], {-16/17, -11/34}], {2, 0}}, 
     {AlgebraicNumber[Sqrt[2], {31/17, 151/68}], {3, 0}}, Sentinel[4, 0], Sentinel[4, 1]}, 
     {{1, {1, 0}}, {AlgebraicNumber[Sqrt[2], {-11/68, -135/68}], {2, 0}}, 
     {AlgebraicNumber[Sqrt[2], {967/136, 31/68}], {3, 0}}, Sentinel[4, 0], Sentinel[4, 1]}}
   In[364]:= SeriesSolutionBasis[x*Der[x]+3, 0, 2] 
   Out[364]= {{{1, {-3, 0}}, Sentinel[0, 0]}}
   In[365]:= SeriesSolutionBasis[x*Der[x]+3, 0, 20] 
   Out[365]= {{{1, {-3, 0}}, Sentinel[18, 0]}}
   In[366]:= SeriesSolutionBasis[Annihilator[Log[x]][[1]],0,1]
   Out[366]= {{{1, {0, 0}}, Sentinel[2, 0], Sentinel[2, 1]}, 
     {{1, {0, 1}}, Sentinel[2, 0], Sentinel[2, 1]}}
 **)
SeriesSolutionBasis[L_, alpha_, n_Integer] := 
  Module[ {ii, lc, k, exp, e, seen, ansatz, a, sys, sol, r, d, vars},
    If[alpha =!= 0, 
      Return[SeriesSolutionBasis[ChangeOfVariables[L, alpha], 0, n]]
    ];
    r = Exponent[L, Der[x]];
    ii = ValuationCorrection[L, alpha];
    lc = Coefficient[#, x, Exponent[#, x, Min]]&[Numerator[Together[ApplyOreOperator[L, (x-alpha)^k]/(x-alpha)^k] /. x -> x + alpha]]; (* indicial polynomial *)
    exp = Flatten[Rest[FactorList[lc]] /. {u_, v_Integer} :> Table[u,{v}]]; (* exponents *)    
    exp = Flatten[Table[ToNumberField[Root[Function[Evaluate[exp[[i]] /. k -> #]], j]], {i, 1, Length[exp]}, {j, 1, Exponent[exp[[i]], k]}]];
    (* break into ZZ-equivalence classes *)
    e = {};
    Do[
      seen = False;
      Do[
        If[IntegerQ[e[[j,1]]-exp[[i]]], 
          AppendTo[e[[j]], exp[[i]]]; seen = True; Break;
        ], 
      {j, 1, Length[e]}];
      If[ !seen, AppendTo[e, {exp[[i]]}] ];
    , {i, 1, Length[exp]}];
    (* determine gaps and log degrees *)
    m = Table[
      e[[i]] = Sort[e[[i]] - e[[i,1]]] + e[[i, 1]];
      e[[i, -1]] - e[[i, 1]]      
    , {i, 1, Length[e]}];
    d = (Length[#]-1)& /@ e;
    (* determine coefficients *)
    sol = {};
    Do[
      ansatz = Sum[a[i,j](x-alpha)^(i + e[[k,1]]) Log[x-alpha]^j, {i,0,m[[k]]+n},{j,0,d[[k]]}];
      sys = Flatten[Table[{a[i,j],Term[i+e[[k,1]],j]}, {i,0,m[[k]]+n},{j,0,d[[k]]}], 1] /. First[Solve[Thread[Flatten[CoefficientList[PolynomialRemainder[Expand[#], x^(m[[k]]+n+1), x], x]& /@ CoefficientList[ApplyOreOperator[L, ansatz]/(x-alpha)^(e[[k,1]]-r+ii) /. x -> x + alpha, Log[x]]]==0], Flatten[Table[a[i,j],{i,0,m[[k]]+n},{j,0,d[[k]]}]]]];
      vars = Union[Cases[sys, a[__], Infinity]];
      Do[
        AppendTo[sol, DeleteCases[Join[sys, Table[Sentinel[m[[k]]+n+1+e[[k,1]], j],{j,0,d[[k]]}]] /. vars[[i]] -> 1 /. a[__] -> 0, {0,_}]];
      , {i, 1, Length[vars]}];      
    , {k, 1, Length[e]}];
    Return[sol];
  ];

(* true iff the term x^u Log[x]^v is integral *)
StandardFilter[_[u_, v_]] := (v == 0 && Re[N[u]] >= 0 || v > 0 && Re[N[u]] > 0)

(**
 INPUT:
   L... an operator L(x,Der[x])
   alpha... a number or Infinity
 OUTPUT:
   L(x+alpha,Der[x])
 **)
Subs[L_, alpha_] :=
  If[ MemberQ[{Infinity,-Infinity,ComplexInfinity}, alpha], 
    Module[ {g, u},
      ToOrePolynomial[Numerator[Together[(ApplyOreOperator[L, g[1/x]] /. x -> 1/x)/x^100]], g[x], OreAlgebra[Der[x]]]
    ]
  , 
    Module[ {coeffs},
      coeffs = CoefficientList[Normal[L], Der[x]] /. x -> x + alpha;
      ToOrePolynomial[Sum[coeffs[[i]]**Der[x]^(i-1), {i, 1, Length[coeffs]}], OreAlgebra[Der[x]]]
    ]
  ];

(**
 INPUT:
   sers... a matrix M of series.
   filter... a function which applied to a pair {i,j} gives True iff x^i Log[x]^j is to be considered integral.
 OUTPUT:
   a vector v={const..., 1}/x such that M.v is a vector of integral series,
   or $Failed if no such vector exists. 
 THROWS: 
   an exception "not enough terms" if the truncation order of the components of M 
   is insufficient.
 EXAMPLES:
   ...
 **)
KillXIfPossible[sers_, filter_:StandardFilter] := 
  Module[ {sys, vars, badterms, r, v},
    r = Length[sers];
    If[Not[And@@(filter/@Cases[sers, Sentinel[u_,v_]->{u-1,v}, Infinity])], 
      Throw["not enough terms"]];
    badterms = Select[Union[Cases[sers, _Term, Infinity]], !filter[Term[#[[1]]-1,#[[2]]]]&];
    sys = Flatten[Table[
      Sum[c[i]Plus@@Cases[sers[[i, j]], {u_, badterms[[k]]} -> u], {i, 1, r}]==0
    , {j, 1, Length[sers[[1]]]}, {k, 1, Length[badterms]}]];
    sol = Solve[sys /. c[r] -> 1];
    Return[If[Length[sol]===0, $Failed, (Array[c, r] /. c[r]->1)/x /. First[sol] /. c[_] -> 0]];
  ];

(**
 INPUT:
   L... an element of OreAlgebra[Der[x]]
   alpha... an AlgebraicNumber object, or a rational number. Defaults to zero
   filter... a function which applied to a pair {i,j} gives True iff x^i Log[x]^j is to be considered integral.
   n... number of terms to be used in the series expansion. if it turns out to be too small, the code will keep restarting the calculation with higher choices of n until n is large enough.
 OUTPUT:
   A list of operators {L[1],...,L[r-1]} with the property that an element M of C((x))[D]/<L>
   is integral if and only if there are formal power series c[1],...,c[r-1] such that 
   M = c[1]L[1] + ... + c[r-1]L[r-1].
 EXAMPLES:
   In[410]:=LocalIntegralBasis[Annihilator[x^(-2)*Exp[x]+x^2/(1-x),Der[x]][[1]]]
   Out[410]={x^2, 1/x**Der[x] + (2/x^2-1/x)}
   In[417]:= LocalIntegralBasis[Annihilator[x^(-2)*Exp[x]+x^2/(1-x),Der[x]][[1]], 1]
   Out[417]= {-1 + x, (-1 + x)**Der[x] + 1}
   In[423]:= LocalIntegralBasis[Annihilator[x^(1/2)+1,Der[x]][[1]], 0]
   Out[423]= {1, x*Der[x]}
   In[424]:= LocalIntegralBasis[Annihilator[x^(3/2)+1,Der[x]][[1]], 0]
   Out[424]= {1, Der[x]}
   In[425]:= LocalIntegralBasis[Annihilator[x Log[x],Der[x]][[1]], 0]
   Out[425]= {1, Der[x]  - 1/x}
   In[426]:= LocalIntegralBasis[Annihilator[Log[x],Der[x]][[1]], 0]
   Out[426]= {x, x*Der[x] }
   In[470]:= LocalIntegralBasis[Annihilator[Exp[x]+Exp[2x]/x+Exp[3x]/x^3,Der[x]][[1]], 0]
   Out[470]= {x^3, 3*x - 3*x^2 + x^2*Der[x], 3 - 6*x + (5*x - 3*x^2)*Der[x] + x^2*Der[x]^2}
 **)
LocalIntegralBasis[L_, alpha_:0, filter_:StandardFilter, n_Integer:10] := 
  Module[ {sols, sers, out, op, e, terms},
    vars = Complement[Variables[Normal[L]], {x, Der[x]}];
    If[ Length[vars] > 0, Return[CRA[LocalIntegralBasis, {L, alpha, filter, n}, vars]] ];
    If[ alpha =!= 0, Return[Subs[#, -alpha]& /@ LocalIntegralBasis[Subs[L, alpha], 0, filter, n]]];
    out = Catch[ (* exception is thrown when expansion order n was too small *)
      sols = SeriesSolutionBasis[L, alpha, n];
      If[ Length[sols] =!= Exponent[L, Der[x]], 
         Print["operator is not fuchsian at expansion point"]; Return[$Failed]
      ];
      sers = {sols};
      (* find smallest power e of x that makes all solutions integral *)
      terms = Cases[sers, _Term, Infinity];
      e = 0;
      While[ And@@(filter/@terms), e = e - 1; terms = terms /. Term[u_,v_Integer] -> Term[u-1,v] ];
      While[ Or@@((!filter[#]&)/@terms), e = e + 1; terms = terms /. Term[u_,v_Integer] -> Term[u+1,v] ];
      out = {ToOrePolynomial[x^e, OreAlgebra[Der[x]]]}; 
      sers = {SeriesSolutionApply[out[[1]], #]& /@ sols};
      Do[
        (* find basis element 1/x^e * Der[x]^i + ... *)
        done = False;
        AppendTo[out, x**Der[x]**Last[out]]; (* first conservative candidate *)
        AppendTo[sers, SeriesSolutionApply[x**Der[x], #]& /@ Last[sers]];
        While[!done, (* refine as much as possible *)
          op = KillXIfPossible[sers];
          If[ op === $Failed, done = True, 
            (* update operator candidate and the corresponding series *)
            out[[i+1]] = Sum[op[[j]]**out[[j]], {j, 1, i+1}];
            sers[[i+1]] = SeriesSolutionApply[out[[i+1]], #]& /@ sols;
          ];
        ];
      , {i, 1, Exponent[L, Der[x]] - 1}];
      out
    ];
    Return[If[StringQ[out], LocalIntegralBasis[L, alpha, filter, n + 5], out]];
  ];

(**
 INPUT:
   L... an element of OreAlgebra[Der[x]]
   filter... a function which applied to a pair {i,j} gives True iff x^i Log[x]^j is to be considered integral.
   n... number of terms to be used in the series expansion. if it turns out to be too small, the code will keep restarting the calculation with higher choices of n until n is large enough.
 OUTPUT:
   A list of operators {L[1],...,L[r-1]} with the property that an element M of C(x)[D]/<L>
   is integral if and only if there are polynomials c[1],...,c[r-1] such that 
   M = c[1]L[1] + ... + c[r-1]L[r-1].
 EXAMPLES:
   In[746]:= GlobalIntegralBasis[Annihilator[Exp[x^3]/x+1/(1-x)^2, Der[x]][[1]]]
   Out[746]= {x - 2*x^2 + x^3, (-9 + 27*x + 9*x^2 - 6*x^3 - 7*x^4 + 5*x^5 - x^6)/(9*(1 + x
      - 3*x^3 + 3*x^4)) + ((-1 + x)*x)/(1 + x - 3*x^3 + 3*x^4)**Der[x]}
 **)
GlobalIntegralBasis[L_, filter_:StandardFilter, n_Integer:5] := 
  Module[ {sols, sers, out, op, e, terms, minpolys, alphas, d, p, q, vars, t},
    vars = Complement[Variables[Normal[L]], {x, Der[x]}];
    If[ Length[vars] > 0, Return[CRA[GlobalIntegralBasis, {L, filter, n}, vars]] ];
    out = Catch[ (* exception is thrown when expansion order n was too small *)
      minpolys = First /@ Rest[FactorList[LeadingCoefficient[L]]]; 
      alphas = ToNumberField[Root[Function[x, #], 1]]& /@ minpolys; (* list of singularities, up to conjugates *)
      sols = SeriesSolutionBasis[L, #, n]& /@ alphas;
      If[ Union[Length /@ sols] =!= {Exponent[L, Der[x]]}, 
         Print["operator is not fuchsian at all finite places"]; Return[$Failed]
      ];
      sers = {#}& /@ sols;
      If[ Length[alphas] === 0, Return[ Table[ToOrePolynomial[Der[x]^i, OreAlgebra[Der[x]]], {i, 0, Exponent[L, Der[x]]-1}] ] ];
      (* first element: prod minpolys[[i]]^e[i], for the smallest integers e[i] that make all the local solutions at alphas[[i]] integral *)
      out = 1;
      Do[
        terms = Cases[sers[[i]], _Term, Infinity];
        e = 0;
        While[ And@@(filter/@terms), e = e - 1; terms = terms /. Term[u_,v_Integer] -> Term[u-1,v] ];
        While[ Or@@((!filter[#]&)/@terms), e = e + 1; terms = terms /. Term[u_,v_Integer] -> Term[u+1,v] ];
        out *= minpolys[[i]]^e
      , {i, 1, Length[alphas]}];
      out = {ToOrePolynomial[out, OreAlgebra[Der[x]]]}; 
      sers = Table[{SeriesSolutionApply[out[[1]], #, alphas[[i]]]& /@ sols[[i]]}, {i, 1, Length[alphas]}];
      (* sers[[i,j,k]] == out[[j]] applied to k-th local solution at i-th singularity *)
      Do[
        (* find basis element 1/x^e * Der[x]^i + ... *)
        done = Table[False, {Length[alphas]}];
        AppendTo[out, (Times@@minpolys)**Der[x]**Last[out]]; (* first conservative candidate *)
        Do[
          AppendTo[sers[[j]], SeriesSolutionApply[out[[i+1]], #, alphas[[j]]]& /@ sols[[j]]];
        , {j, 1, Length[alphas]}];
        While[!And@@done, (* refine as much as possible *)
          Do[
            If[ !done[[k]],
              op = KillXIfPossible[sers[[k]]];
              If[ op === $Failed, done[[k]] = True, 
                (* globalize *)
                d = Exponent[minpolys[[k]], x]; 
                If[ d === 1,
                  op = op /. x -> x - alphas[[k]]
                ,
                  op = op /. x -> 1;
                  op = Table[If[Head[op[[j]]]===AlgebraicNumber, 
                    op[[j, 2]].(x^(Range[d] - 1))
                  , 
                    op[[j]]
                  ], {j, 1, Length[op]}]/minpolys[[k]];
                ];
                (* update operator candidate and the corresponding series *)
                out[[i+1]] = Together[Sum[op[[j]]**out[[j]], {j, 1, i+1}]];
                Do[sers[[j,i+1]] = SeriesSolutionApply[out[[i+1]], #, alphas[[j]]]& /@ sols[[j]],
                        {j, 1, Length[alphas]}];
              ];
           ];
          , {k, 1, Length[alphas]}];
        ];
      , {i, 1, Exponent[L, Der[x]] - 1}];
      (* autoreduce *)
      d = PolynomialLCM@@(Denominator /@ Together /@ Normal /@ out);
      out = Together[d*(Normal /@ out)];
      Do[
        Do[
          p = Coefficient[out[[i]], Der[x], j - 1];
          q = Coefficient[out[[j]], Der[x], j - 1]; (* nonzero by construction *)
          out[[i]] = Numerator[Together[out[[i]] - PolynomialQuotient[p, q, x]*out[[j]]]]; (* denominators can only be constants, and they don't matter *)
        , {j, i - 1, 1, -1}];
      , {i, 2, Length[out]}];
      Together[((1/d)**ToOrePolynomial[#, OreAlgebra[Der[x]]])& /@ out]
    ];
    Return[If[StringQ[out], GlobalIntegralBasis[L, filter, n + 3], out]];    
  ];

(**
 INPUT: A function f, a list of arguments, and a list of variables
 OUTPUT: result of chinese remaindering and rational reconstruction on the outputs of f applied to the arguments with the variables replaced by integers. It is assumed that the output of f is a list of operators in x and Der[x].
 **)
CRA[f_, args_, vars_] := 
  Module[ {t, mod, imgs, p, q},
    If[ Length[vars] == 0, Return[ f@@args ] ];
    t = First[vars]; mod = {}; imgs = {}; p = 7; out = Null;
    While[ True,
      p += 1; 
      AppendTo[mod, p]; 
      AppendTo[imgs, (#.q^(Range[Length[#]]-1))&[Normal /@ f@@(args /. t -> p)]];
      If[ Together[(out /. t -> p) - Last[imgs]] === 0, 
        Return[ToOrePolynomial[Collect[#, Der[x], Together], OreAlgebra[Der[x]]]& /@ CoefficientList[out, q]];
      ];
      (* this assumes that the output of f is already monic. to use the monic-maker in Lift,
         we must not merge the list into a polynomial wrt. q but instead lift each operator separately *)
      Catch[out = Lift[imgs, mod, Join[{q, x, Der[x]}, Rest[vars]], t, 0]];
    ];
  ];


(**
 INPUT: 
   L... an element of OreAlgebra[Der[x]]
   filter... a function which applied to a pair {i,j} gives True iff x^i Log[x]^j is to be considered integral.
   n... number of terms to be used in the series expansion. if it turns out to be too small, the code will keep restarting the calculation with higher choices of n until n is large enough.
 OUTPUT:
   A list of operators {L[1],...,L[r-1]} that form a global integral basis
   of C(x)[D]/<L> which is normal at infinity.
 EXAMPLES:
   ...
 **)
GlobalIntegralBasisNormalAtInfinity[L_, filter_:StandardFilter, m_Integer:5] := 
   Module[ {w, v, n, k, M, Mhat, N, c, i0},
     w = GlobalIntegralBasis[L, filter, m];
     v = LocalIntegralBasis[L, Infinity, filter, m];
     If[ w === $Failed || v === $Failed, Return[$Failed] ];
     n = Length[w]; 
     (* w[i] == sum( M[i,j]*v[j], j=1..n ) *)
     M = Together[Table[Coefficient[w[[i]], Der[x], j], {i, 1, n}, {j, 0, n-1}] . 
          Inverse[Table[Coefficient[v[[i]], Der[x], j], {i, 1, n}, {j, 0, n-1}]]];
     While[ True, 
       Do[
         k[i] = Max[(Exponent[Numerator[#],x]-Exponent[Denominator[#],x])& /@ DeleteCases[M[[i]], 0]];
       , {i, 1, n}];
       N = Limit[DiagonalMatrix[Table[x^(-k[i]), {i, 1, n}]].M, x -> Infinity];
       c = NullSpace[Transpose[N]]; 
       If[ Length[c] == 0, Return[ w ] ]; (* DONE! *)
       c = First[c];
       i0 = 0; Do[If[c[[i]] != 0 && (i0 == 0 || k[i0] > k[i]), i0 = i], {i, 2, n}]; 
       w[[i0]] = Sum[c[[i]]x^(k[i0] - k[i])w[[i]], {i, 1, n}];
       M[[i0]] = Together[Sum[c[[i]]x^(k[i0] - k[i])M[[i]], {i, 1, n}]];
     ];
   ];

(* ================== borrowed from LinearSystemSolver.m ============================ *)

(** ------------------------------------------------------------------- **)
(* Arithmetic *)

List2Poly[coeffs_List, var_] := coeffs . var^(Range[Length[coeffs]]-1);
Poly2List[p_, var_, deg_] := Module[ {l}, 
   l = CoefficientList[p, var]; 
   If[ Length[l] <= deg + 1, 
       Return[Join[l, Table[0, {deg + 1 - Length[l]}]]],
       Return[Take[l, deg + 1]]
   ]];

(**
 * polynomial division
 **)
QuoRem[p_, q_, x_, m_] :=
  Module[ {p0, q0, quo, c, i, j},

    p0 = CoefficientList[p, x]; q0 = CoefficientList[q, x]; quo = {};

    If[ Length[p0] < Length[q0], Return[ {0, p} ] ];

    While[ Length[p0] >= Length[q0],

      c = PolynomialMod[Last[p0]/Last[q0], m];
      PrependTo[quo, c];

      j = Length[p0] - Length[q0] + 1;
      Do[ p0[[j++]] = p0[[j]] - c q0[[i]], {i, 1, Length[q0]} ]; 
      p0 = Most[p0];
    ];

    Return[ {List2Poly[quo, x], List2Poly[p0, x]} ]
  ];

MyPolynomialQuotient[p_, q_, x_, m_] := First[QuoRem[p, q, x, m]];
MyPolynomialRemainder[p_, q_, x_, m_] := Last[QuoRem[p, q, x, m]];

(** ------------------------------------------------------------------- **)
(* Reconstruction *)

Lift[rats_, points_, vars_, x_, p_Integer] :=
  Module[ {u, myvars, data, den, terms, lt, res, deg},
    If[ Length[rats] =!= Length[points], Throw["illegal argument"] ];
    myvars = Append[vars, u];
    data = PolynomialSupport[#, myvars, Modulus -> p]& /@ 
          (Numerator[#] + u Denominator[#]&) /@ Together[rats, Modulus -> p]; 
    If[ Length[Union[Length /@ data]] =!= 1, Throw["unexpected zeros."] ]; 
    terms = (#/(#/.Thread[myvars->1]))&[data[[1]]];
    (* normalize *)
    lt = Position[terms, Last[Sort[terms]]][[1, 1]];
    data = Transpose[#/#[[lt]]& /@ (data /. Thread[myvars -> 1])];
    (* find denominator and clear it *)
    den = Sum[Prime[500+i]data[[i]], {i, 1, Length[terms]}];
    den = InterpolatingPolynomial[Transpose[{points, den}], x, Modulus -> p];
    den = ReconstructRatfun[den, points, x, p];
    deg = 1 + Exponent[Numerator[den], x]; den = Denominator[den];
    data = Transpose[Table[data[[All, i]]*(den /. x -> points[[i]]), {i, 1, Length[points]}]];
    (* interpolation *)
    (#1/#2)&@@CoefficientList[Table[Expand[InterpolatingPolynomial[Transpose[Take[#, deg]& /@ {points, data[[i]]}], x, Modulus -> p], Modulus -> p], {i, 1, Length[terms]}].terms, u]
  ];
Lift[rats_, points_, vars_, opts:((_Rule|_RuleDelayed)...)] :=
  Module[ {u, myvars, data, den, terms, lt, res, deg, p, nondefective},
    recon = "recon" /. {opts} /. {"recon" -> ReconstructQ0};
    If[ Length[rats] =!= Length[points], Throw["illegal argument"] ];
    myvars = Append[vars, u];
    data = Table[PolynomialSupport[(Numerator[#]+u Denominator[#]&)[Together[rats[[i]], Modulus -> points[[i]]]], myvars, Modulus -> points[[i]]], {i, 1, Length[points]}];
    If[ Length[Union[Length /@ data]] =!= 1, 
       nondefective = Position[Length /@ data, Max[Length /@ data]];
       Print["discarding ", Length[points] - Length[nondefective], " images."];
       Return[Lift[Extract[rats, nondefective], Extract[points, nondefective], vars, opts]];
    ]; 
    terms = (#/(#/.Thread[myvars->1]))&[data[[1]]];
    (* normalize *)
    lt = Position[terms, Last[Sort[terms]]][[1, 1]];
    data = Transpose[#/#[[lt]]& /@ (data /. Thread[myvars -> 1])];
    data = Transpose[Table[PolynomialMod[data[[All, i]], points[[i]]], {i, 1, Length[points]}]];
    (* reconstruct one by one *)
    data = Table[recon[ChineseRemainder[data[[i]], points], Times@@points], {i, 1, Length[terms]}];
    (* data *= LCM@@(Denominator /@ data); *)
    (#1/#2)&@@CoefficientList[data.terms, u]
  ];

PolynomialSupport[poly_, vars_, opts___] := (* multivariate polynomial expression to list of monomials *)
  Module[ {x, rest, terms},
    If[ poly === 0, Return[ {} ] ];
    x = First[vars]; rest = Rest[vars];
    terms = CoefficientList[poly, x, opts];
    If[ Length[rest] > 0, terms = PolynomialSupport[#, rest, opts]& /@ terms];
    DeleteCases[Flatten[terms*x^Range[0, Exponent[poly, x, opts]]], 0]
  ];

(**
 * Reconstruction of rational numbers
 **)
ReconstructQ[n_, pq_] := (#[[1]]/#[[2]])&[First[LatticeReduce[{{n, 1}, {pq, 0}}]]];

ReconstructQ0[n_, pq_] := If[ n===0, 0, (((#[[2,2]]/#[[1,2,2]])&)[Internal`HGCD[pq, Mod[n,pq]]]*2)/2 ];

(* use this if you expect u : v to be close to  #digits in numerator : #digits in denominator. *)
ReconstructQbiased[u_, v_][n_, q_] := If[ n==0, 0,
  Module[ {r, s, rr, ss, quo},
    {r, s, rr, ss} = {q, 0, n, 1};
    While[ v Log[N[1 + Abs[rr]]] > u Log[N[1 + Abs[ss]]],
      quo = Quotient[r, rr];
      {r, s, rr, ss} = {rr, ss, r - quo rr, s - quo ss}
    ];
    rr/ss
  ]];

(* this gives the smallest of all *)
ReconstructQ2[n_, q_] := If[ n==0, 0,
  Module[ {r, s, rr, ss, quo, u, v},
    {u, v} = {n, 1}; 
    {r, s, rr, ss} = {q, 0, Mod[n, q], 1};
    While[ rr != 0, 
      quo = Quotient[r, rr];
      {r, s, rr, ss} = {rr, ss, r - quo rr, s - quo ss};
      If[ s != 0 && Abs[r*s] < Abs[u*v], {u, v} = {r, s} ]
    ];
    u/v
  ]];

(**
 * Reconstruction of rational functions
 **)
Do[T[i]=0,{i,1,6}];
ReconstructRatfun[g_, mod_, x_, p_] := 
  Module[ {t, r},
    {t, r} = Timing[MyReconstructRatfun[g, mod, x, p]];
    T[1] += t;
    Return[r];    
  ];

MyReconstructRatfun[g_, mod_, x_, p_] :=
  Module[ {t, f, r0, r1, t0, t1, n, d, q, c, df, drat, dr1, dt1, unique},

    c = PolynomialMod[#, p]&;
    If[ c[g] === 0, Return[ 0 ] ];

    f = If[ ListQ[mod], Product[x - mod[[i]], {i, 1, Length[mod]}], mod ];
    df = Exponent[f, x];
    {r0, r1, t0, t1} = {f, g, 0, 1}; {n, d} = {r1, t1};
    drat = Exponent[n, x] + Exponent[d, x];
    unique = True;

    While[ r1 =!= 0,

      t = First[Timing[
      dr1 = Exponent[r1, x]; dt1 = Exponent[t1, x];
      If[ dr1 < df && t1 =!= 1 && drat == dr1 + dt1, unique = False];
      If[ dr1 < df && drat > dr1 + dt1,
        {n, d} = {r1, t1}; drat = dr1 + dt1;
        unique = True;
      ]; 
      ]];
      T[5]+=t;

      {t, q} = Timing[MyPolynomialQuotient[r0, r1, x, p]];
      T[2]+=t;
      {t, {r0, r1, t0, t1}} = Timing[{r1, c[r0 - q r1], t1, c[t0 - q t1]}];
      T[4]+=t;
    ];
    If[ !unique, Throw["ambigous reconstruction result"] ];
    
    {t, {n, d}} = Timing[CoefficientList[#, x]& /@ {n, d}];
    T[3]+=t;
    {t, {n, d}} = Timing[Map[c, {n, d}/Last[d], {2}]];
    T[6]+=t;
    {n, d} = List2Poly[#, x]& /@ {n, d};

    Return[Together[n/d, Modulus -> p]];
  ];
