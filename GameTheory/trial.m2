newPackage(
   "GameTheory",
   Version => "0.1",
   Date => "April, 2025",
   Authors => {
      {Name => "Lars Kastner",
         Email => "kastner@math.tu-berlin.de",
         HomePage => "https://lkastner.github.io"},
      {Name => "Elke Neuhaus",
         Email => "elke.neuhaus@mis.mpg.de",
         HomePage => "https://sites.google.com/view/elkeneuhaus"},
      {Name => "Irem Portakal",
         Email => "mail@irem-portakal.de",
         HomePage => "https://www.irem-portakal.de"},
      {Name => "",
         Email => "",
         HomePage => ""},,
      {Name => "",
         Email => "",
         HomePage => ""},,
      {Name => "",
         Email => "",
         HomePage => ""},,
      {Name => "",
         Email => "",
         HomePage => ""},,
      {Name => "",
         Email => "",
         HomePage => ""},,
      {Name => "",
         Email => "",
         HomePage => ""},
   },
   Headline => "A package for computing equilibria in game theory",
   Keywords => {"Game Theory","Equilibria","Nash","Correlated","Dependency","Spohn","Conditional Independence"},
   PackageExports => {"Polyhedra","GraphicalModels"},
   PackageImports => {"Polyhedra"}
   )

export {
   "enumerateTensorIndices",
   "Tensor",
   "zeroTensor",
   "randomTensor",
   "slice",
   "getVariableToIndexset",
   "assemblePolynomial",
   "assemblePlayeriPolynomials",
   "correlatedEquilibria"
}



--***************************************--
--  Methods for correlated equlilibria   --
--***************************************--



---------------------------------------------------
-- enumerateTensorIndices ZZ
-- enumerateTensorIndices List
--
-- Returns the list of index tuples for a tensor 
-- with the given dimensions.
--
-- Note: Indices start at 0 and go up to d_i-1,
-- where d_i is the i-th element of the input list.
---------------------------------------------------

enumerateTensorIndices = method()
enumerateTensorIndices ZZ := z -> apply(toList (0..z-1), e->{e})
enumerateTensorIndices List := s -> (
   if length s == 1 then 
      return enumerateTensorIndices s#0
   else
      start := enumerateTensorIndices s#0;
      ri := toList (1..(length(s)-1));
      rest := enumerateTensorIndices s_ri;
      result := {};
      for s in start do
         for r in rest do
            result = append(result, join(s,r));
      result
)

---------------------------------------------------------
-- Defines a new type "Tensor" based on MutableHashTable.
---------------------------------------------------------

Tensor = new Type of MutableHashTable

-----------------------------------------------------------
-- zeroTensor (Ring, List)
--
-- The method creates a zero tensor with the given format and ring.
-----------------------------------------------------------

zeroTensor = method()
zeroTensor List := dims -> zeroTensor(QQ,dims)
zeroTensor(Ring,List) := (R,dims) -> (
   result := new Tensor;
   indexset := enumerateTensorIndices dims;
   for i in indexset do
      result#i = 0_R;
   result#"format" = dims;
   result#"coefficients" = R;
   result#"indexes" = indexset;
   result
)

---------------------------------------------------------------------
-- randomTensor (Ring, List)
--
-- The method creates a random tensor with the given format and ring.
---------------------------------------------------------------------


randomTensor = method()
randomTensor List := dims -> randomTensor(QQ,dims)
randomTensor(Ring,List) := (R,dims) -> (
   result := new Tensor;
   indexset := enumerateTensorIndices dims;
   for i in indexset do
      result#i = random R;
   result#"format" = dims;
   result#"coefficients" = R;
   result#"indexes" = indexset;
   result
)

----------------------------------------------
-- format Tensor
--
-- It prints the format of the defined tensor.
----------------------------------------------

format Tensor := T -> T#"format"
coefficientRing Tensor := T -> T#"coefficients"
indexset = method()
indexset Tensor := T -> T#"indexes"

------------------------------------------------------
-- slice (Tensor, List, List)
--
-- The first list (Lstart) specifies the fixed indices 
-- before the varying position, and the second list 
-- (Lend) specifies the fixed indices after it.
--
-- The method varies the index at the position 
-- given by the length of Lstart, from 0 to d_i-1, 
-- where d_i is the corresponding dimension size.
-----------------------------------------------------


slice = method()
slice (Tensor, List, List) := (T, Lstart, Lend) -> (
   dims := format T;
   iteratingPosition := length Lstart;
   result := {};
   for i from 0 to dims#iteratingPosition -1 do (
      mindex := join(Lstart, {i}, Lend);
      result = append(result, T#mindex);
   );
   result
)


---------------------------------------------------
-- getVariableToIndexset(Ring, List)
--
-- Given a ring R and a list ki representing the
-- indices,returns the corresponding generator.
---------------------------------------------------


getVariableToIndexset = method()
getVariableToIndexset(Ring, List) := (R, ki) -> (
   p := position(apply(gens R, i -> last baseName i), i -> i == ki);
   R_p
)


--------------------------------------------------------
-- assemblePolynomial(Ring, Tensor, List)
--
-- Constructs a single linear inequality (polynomial)
-- representing a deviation condition for correlated 
-- equilibrium constraints.
--
-- Inputs:
--   - PR: Polynomial ring containing variables p_{...}
--   - Xi: Tensor of strategy probabilities
--   - ikl: A list {i, k, l} where:
--        i = player index
--        k = current strategy
--        l = deviating strategy
-------------------------------------------------------


assemblePolynomial = method()
assemblePolynomial(Ring, Tensor, List) := (PR, Xi, ikl) -> (
   FBi := indexset Xi;
   reverseVarMap := new MutableHashTable;
   for k in FBi do (
      reverseVarMap#k = getVariableToIndexset(PR, k);
   );
   i := ikl#0;
   k := ikl#1;
   l := ikl#2;
   use PR;
   kindices := select(FBi, e->e#i==k);
   lindices := select(FBi, e->e#i==l);
   kterm := sum apply(kindices, ki -> Xi#ki*reverseVarMap#ki);
   lterm := sum apply(lindices , li->(tmp := new MutableList from li; tmp#i=k; a := toList tmp; Xi#li*reverseVarMap#a));
   ineq := kterm-lterm;
   ineq
)

-----------------------------------------------------
-- assemblePlayeriPolynomials(Ring, Tensor, ZZ)
--
-- Returns a list of all polynomials for a given
-- player i in a correlated equilibrium.
-----------------------------------------------------


assemblePlayeriPolynomials = method()
assemblePlayeriPolynomials(Ring, Tensor, ZZ) := (PR, Xi, i) -> (
   result := {};
   di := (format Xi)#i;
   for k from 0 to di-1 do (
      for l from 0 to di-1 do (
         poly := assemblePolynomial(PR, Xi, {i,k,l});
         result = append(result, poly);
      );
   );
   result
)

--------------------------------------------------------------
-- correlatedEquilibria(List)
--
-- Inputs:
--   - X: A list of tensors, one for each player's payoff

-- Assembles all incentive constraint polynomials and returns
-- a polytope by adding the probability constraints.
-------------------------------------------------------------


correlatedEquilibria = method()
correlatedEquilibria List := X -> (
   F := coefficientRing (X#0);
   FBi := indexset (X#0);
   p := getSymbol "p";
   PR := F[apply(FBi, fb->p_fb)];
   nplayers := length format X#0;
   L := flatten for i from 0 to nplayers-1 list assemblePlayeriPolynomials(PR, X#i, i);
   polyDim := length FBi;
   vectors := {};
   ineqs := for p in L list apply(generators PR, g -> coefficient(g, p));
   ineqs = (matrix ineqs) || (map identity (F^(#FBi)));
   ineqsrhs := transpose matrix {toList ((numRows ineqs):0_F)};
   eq := matrix {toList ((numColumns ineqs):1_F)};
   eqrhs := matrix {{1_F}};
   polyhedronFromHData(-ineqs, ineqsrhs,eq,eqrhs)
)



--***************************************--
--  Methods for dependency equlilibria   --
--***************************************--


-- ProbabilityRing = new Type of Ring

probabilityRing = method(Options => { CoefficientRing => QQ, ProbabilityVariableName => "p" })
probabilityRing List := Ring => opts -> Di -> (
    J := enumerateTensorIndices Di;
    p := getSymbol opts.ProbabilityVariableName;
    K := opts.CoefficientRing;
    -- R := new ProbabilityRing;
    R := K[apply(J, j -> p_j)];

    P := zeroTensor(R, Di);
    for j in J do P#j = (p_j)_R;
    R#"probabilityVariable" = P;

    R#"gameFormat" = Di;
    R)

randomGame = method(Options => {CoefficientRing => QQ})
randomGame List := List => opts -> Di -> (
    K := opts.CoefficientRing;
    apply(length Di, i -> randomTensor(K, Di)))

genericGame = method()
genericGame Ring := List => PPR -> (
    Di := PPR#"gameFormat";
    x := PPR#"payoffVariable";
    apply(#Di, i -> (result := new Tensor;
                     J := enumerateTensorIndices Di;
                     apply(J, j -> result#j = x_i#j);
                     result#"format" = Di;
                     result#"coefficients" = PPR;
                     result#"indexes" = J;
                     result)))

spohnMatrices = method()
spohnMatrices (Ring, List) := List => (PR, X) -> (
    p := PR#"probabilityVariable";
    n := length X;
    d := format X_0;
    J := indexset X_0;
    apply(n, i -> matrix apply(d_i, k -> {sum(select(J, j -> j_i==k), j -> p#j),
                                          sum(select(J, j -> j_i==k), j -> (X_i)#j * p#j) })))

spohnIdeal = method()
spohnIdeal (Ring, List) := List => (PR, X) -> (
    M := spohnMatrices(PR, X);
    sum(M, m -> minors(2, m)))

konstanzMatrix = method(Options=>{ KonstanzVariableName => "k" })
konstanzMatrix (Ring, List) := Matrix => opts -> (PR, X) -> (
    k := getSymbol opts.KonstanzVariableName;
    Di := PR#"gameFormat";
    p := PR#"probabilityVariable";
    n := #Di;
    J := enumerateTensorIndices Di;
    konstanzRing := PR[apply(n, i -> k_i)];
    M := spohnMatrices(PR, X);
    LinearForms := apply(n, i -> (M_i * matrix{{(k_i)_konstanzRing}, {-1}} ));
    P := vector(apply(J, j -> p#j));
    fold((M0, M1) -> M0 || M1, 
         apply(n, i -> transpose matrix apply(Di_i,
                                              j -> diff(P, (LinearForms_i)_(j, 0)))))
)



--****************************************************--
--  Methods for conditional independence equlilibria  --
--****************************************************--



------------------------------------------------------------------------
-- toMarkovRing Ring
-- input must be a probabilityRing
------------------------------------------------------------------------

toMarkovRing=method()
toMarkovRing Ring := R -> (
    if not R#?"gameFormat" then error "expected a ring created with probabilityRing";
    d:= R#"gameFormat";
    kk := coefficientRing(R);
    variableName := substring ( 0, 1, toString (gens(R))#0 );
    if variableName == "p" then (
	markovRing(toSequence(d), Coefficients=>kk, VariableName=>"q")
	)
    else (
	markovRing(toSequence(d), Coefficients=>kk)
	)
    )

---------------------------------------------------------------------------------------------------
-- mapToMarkovRing Ring
-- mapToProbabilityRing Ring
-- inputs to both methods must be rings created with probabilityRing
---------------------------------------------------------------------------------------------------

mapToMarkovRing=method()
mapToMarkovRing Ring := R -> (
    markovR := toMarkovRing(R);
    F := map(markovR, R, gens(markovR));
    F
    )

mapToProbabilityRing=method()
mapToProbabilityRing Ring := R -> (
    markovR := toMarkovRing(R);
    F := map(R, markovR, gens(R));
    F
    )

------------------------------------------------------------------------
-- ciIdeal (PR, Stmts, PlayerNames)
-- ciIdeal (PR, Stmts)
-- ciIdeal (PR, G, PlayerNames)
-- ciIdeal (PR, G)
-- gives conditional independence ideal associated to a graogh G
-- or a set of conditional independence statements Stmts
-- as an ideal of the given probabilityRing
--------------------------------------------------------------------------------



ciIdeal = method()
ciIdeal (Ring, List, List) := (PR, Stmts, PlayerNames) -> (
    markovR := toMarkovRing(PR);
    phi := mapToProbabilityRing(PR);
    I := conditionalIndependenceIdeal ( markovR, Stmts, PlayerNames );
    phi I
    )
ciIdeal (Ring, List) := (PR, Stmts) -> (
    markovR := toMarkovRing(PR);
    phi := mapToProbabilityRing(PR);
    I := conditionalIndependenceIdeal ( markovR, Stmts );
    phi I
    )
ciIdeal (Ring, Graph, List) := (PR, G, PlayerNames) -> (
    Stmts := globalMarkov G;
    ciIdeal (PR, Stmts, PlayerNames)
    )
ciIdeal (Ring, Graph) := (PR, G) -> (
    Stmts := globalMarkov G;
    ciIdeal (PR, Stmts)
    )

-----------------------------------------------
-- intersectWithCImodel (V, Stmts, PlayerNames)
-- intersectWithCImodel (V, Stmts)
-- intersectWithCImodel (V, G, PlayerNames)
-- intersectWithCImodel (V, G)
-----------------------------------------------


intersectWithCImodel = method(Options => {Verbose => false})
intersectWithCImodel (Ideal, List, List) := o -> (V, Stmts, PlayerNames) -> (
    v := o.Verbose;
    R := ring V;
    H := map (R,ZZ);
    I := ciIdeal (R, Stmts, PlayerNames);
    if I + V == H(ideal(1)) then (
	result := H(ideal(1));
	result
	);
    for k from 0 to length(R_*)-1 do (
	I = saturate(I,R_k,Strategy=>Bayer);
	if v then print ("Completed step " | k+1 | " of saturating CI ideal");
	V = saturate(V,R_k,Strategy=>Bayer);
	if v then print ("Completed step " |k+1| " of saturating input ideal");
	);
    I = saturate(I,sum(R_*),Strategy=>Bayer);
    if v then print ("Completed step " |length(R_*)+1| " of saturating CI ideal");
    V = saturate(V, sum(R_*), Strategy=>Bayer);
    if v then print ("Completed step " |length(R_*) +1|" of saturating input ideal");
    J := I+V;
    for k from 0 to length(R_*)-1 do (
	J = saturate(J,R_k,Strategy=>Bayer);
	if v then print ("Completed step "|k+1|" of saturating sum");
	);
    J = saturate(J,sum(R_*),Strategy=>Bayer);
    result = J;
    result
    )
intersectWithCImodel (Ideal, List) := o -> (V, Stmts) -> (
    v := o.Verbose;
    d := (ring V)#"gameFormat";
    PlayerNames := toList (1..#d);
    intersectWithCImodel (V, Stmts, PlayerNames, Verbose=>v)
    )
intersectWithCImodel (Ideal, Graph, List) := o -> (V, G, PlayerNames) -> (
    v := o.Verbose;
    Stmts := globalMarkov G;
    intersectWithCImodel (V, Stmts, PlayerNames, Verbose=>v)
    )
intersectWithCImodel (Ideal, Graph) := o -> (V, G) -> (
    v := o.Verbose;
    d := (ring V)#"gameFormat";
    PlayerNames := toList (1..#d);
    intersectWithCImodel (V, G, PlayerNames, Verbose=>v)
    )

--------------------------------------
-- spohnCI (PR, X, G)
-- spohnCI (PR, X, G, PlayerNames)
-- spohnCI (PR, X, Stmts)
-- spohnCI (PR, X, Stmts, PlayerNames)
--------------------------------------


spohnCI = method(Options => {Verbose => false})
spohnCI (Ring, List, Graph) := o -> (PR, X, G) -> (
    v := o.Verbose;
    spohn := spohnIdeal(PR, X);
    intersectWithCImodel(spohn, G, Verbose => v)
    )
spohnCI (Ring, List, Graph, List) := o -> (PR, X, G, PlayerNames) -> (
    v := o.Verbose;
    spohn := spohnIdeal(PR, X);
    intersectWithCImodel(spohn, G, PlayerNames, Verbose => v)
    )
spohnCI (Ring, List, List) := o -> (PR, X, Stmts) -> (
    v := o.Verbose;
    spohn := spohnIdeal(PR, X);
    intersectWithCImodel(spohn, Stmts, Verbose => v)
    )
spohnCI (Ring, List, List, List) := o -> (PR, X, Stmts, PlayerNames) -> (
    v := o.Verbose;
    spohn := spohnIdeal(PR, X);
    intersectWithCImodel(spohn, Stmts, PlayerNames, Verbose => v)
    )


--******************************************--
-- DOCUMENTATION     	       	    	    -- 
--******************************************--

beginDocumentation()

doc ///
  Key
    GameTheory
  Headline
    A package for computing equilibria in game theory 
  Description
  
    Text
      {\bf Game Theory} is a package for several equilibrium concepts in game theory. It constructs the algebraic and
      combinatorial models for Nash, correlated, dependency and conditional independence equilibria.
       
      This package constructs ...
      
      Here is a typical use of this package.  

      
    Text
      
      
    Example
        
      
    Text
      The following people have generously contributed their time and effort to this project:  
      
      Name name<@HREF""@>.
      
  Caveat
     GameTheory requires GraphicalModels.m2...
///;


--------------------------------
-- Documentation randomTensor --
--------------------------------

doc ///
  Key
    randomTensor
    (randomTensor, List)
    (randomTensor, Ring, List)
  Headline
    construct a tensor with random entries from a given ring
  Usage
    randomTensor format
    randomTensor(R, format)
  Inputs
    format: 
      :List 
        A list of integers specifying the format of the tensor (e.g. {2,2,2} creates a 2x2x2 tensor)
    R: 
      @Ring@
        (Optional) A ring from which random coefficients will be drawn.
  Outputs
    :Tensor
      A tensor whose entries are randomly selected elements of the ring.
  Description

    Text
      This method constructs a tensor with the specified format and fills it with random elements from the given ring.
      Internally, it uses a hash table where each key is a multi-index (a list of positions) and the value is a random 
      element from the ring. Metadata such as the format, coefficient ring, and index set are stored in the 
      tensor as well.

    Example
      T = randomTensor {2,2,2}
      T#{0,1,1}
      format T
      peek T

    SeeAlso
      zeroTensor
/// 


----------------------------------------
-- Documentation correlatedEquilibria --
----------------------------------------

doc ///
  Key
    correlatedEquilibria
    (correlatedEquilibria, List)
  Headline
    compute the correlated equilibria polytope for a game
  Usage
    correlatedEquilibria X
  Inputs
    X:
      :List
        A list of tensors, one for each player. Each tensor encodes the payoffs for that player.
  Outputs
    :Polyhedron
      The polytope representing the set of correlated equilibria for the game.
  Description

    Text
      This method constructs and returns the correlated equilibrium polytope for a finite game.
      The input is a list of payoff tensors, one for each player. The tensor at position i gives the payoffs for player i.

    Example
      X1 = zeroTensor(QQ, {2,2});
      X2 = zeroTensor(QQ, {2,2});
      X0#{0,0} = -99; X0#{0,1} = 1; X0#{1,0} = 0; X0#{1,1} = 0;
      X1#{0,0} = -99; X1#{0,1} = 0; X1#{1,0} = 1; X1#{1,1} = 0;
      
      CE = correlatedEquilibria {X1, X2}
      vertices CE
      facets CE

    Example
      X1 = randomTensor(QQ, {2,2,3})
      X2 = randomTensor(QQ, {2,2,3})
      X3 = randomTensor(QQ, {2,2,3})
      
      CE = correlatedEquilibria {X1, X2, X3}
      vertices CE
      dim CE

      
  SeeAlso
    assemblePolynomial
    assemblePlayeriPolynomials
///


-----------------------------------
-- Documentation probabilityRing --
-----------------------------------

doc ///
    Key
        probabilityRing
        (probabilityRing, List)
    Headline
        Ring of probability distributions of a game indexed by ordered multi-indices
    Usage
        probabilityRing(Di)
    Inputs
        Di:List
           a list of natural numbers $d_0,\dots,d_{n-1}$
    -- Optional inputs
    --     CoefficientRing => ..., default value QQ, optional input to choose the base field
    --     ProbabilityVariableName => ..., default value "p", symbol used for the tensor of probability variables
    Outputs
        :Ring  
         a polynomial ring with a tensor of variables $p_{i_0,\dots,i_{n-1}}$
         such that $i_j$ runs from $0$ to $d_j-1$.
    Description
        Text
            The list $Di$ represents the format of the game.
            In this example we create a ring of probability distributions coming from a
            game with format {2, 3, 2}. This format can be accessed from the ring through
            the field "gameFormat".
            
            The variables $p#i$ are the entries of the tensor $p$, which can be
            accessed from the ring through the field "probabilityVariable".

        Example
            Di = {2,1,2};
            PR = probabilityRing Di;
            numgens PR
            pairs PR#"probabilityVariable"
      
        Text 
            The optional argument "CoefficientRing" allows to change the base field. If no choice is
            specified, the base field is set to QQ. It is also possible to change the name of the
            variable tensor through the optional argument "ProbabilityVariableName", which is set to
            the string "p" by default.
 
        Example
            PR2 = probabilityRing (Di, Coefficients=>RR, ProbabilityVariableName=>q);
            coefficientRing PR2
            pairs PR2#"probabilityVariable"
      
        -- Figure out all of the functions which require a probabilityRing
        Text
            -- The functions @TO spohnMatrices@, @TO spohnIdeal@, @TO konstanzMatrix@, ... require the ring to be created by this function
            -- or in a similar manner.
///

------------------------------
-- Documentation randomGame --
------------------------------

doc ///
  Key
    randomGame
    
  Headline
    constructs game of a given format with arbitrary payoffs
  Usage
    randomGame(Di)
  Inputs
    Di:List 
      with positive integer entries $d_1,\dots ,d_n$ describing the format of the game
  --Optional inputs
  --  CoefficientRing => ..., default value QQ, optional input to choose another ring of coefficients
  Outputs
    :List  
      a list of n tensors of format $d_1 \times \dots \times d_n$ that are the payoff tensors of a random game
  Description
    Text 
      The list $Di = \{d_1,\dots ,d_n \}$ represents the format of the game. 
      This example creates a random game of format $2 \times 2$.
      
    Example
      X = randomGame({2,2})
      peek X#1
      peek X#2

    Text
      The optional argument CoefficientRing allows to change the ring of payoffs. 
      If no coefficient choice is specified, the payoffs will be rational numbers.
      This example creates a random game of format $2 \times 2$ with integer coefficients.

    Example
      X = randomGame({2,2}, CoefficientRing => ZZ)
      peek X#1
      peek X#2

    Text
     Outputs of this function can be used as input for the functions spohnMatrices, spohnIdeal and konstanzMatrix. --ADD MORE???

  SeeAlso
    spohnMatrices
    spohnIdeal
    konstanzMatrix
    --ADD MORE?
    
///

---------------------------------
-- Documentation spohnMatrices --
---------------------------------

doc ///
  Key
    spohnMatrices
    
  Headline
    compute the list of Spohn matrices of a given game
  Usage
    spohnMatrices(PR,X)
  Inputs
     PR:Ring 
      a probability ring obtained via probabilityRing(Di), where $Di = \{ d_1, \ldots, d_n \}$ is the format of the game
     X:List 
      a list of n tensors of format $d_1 \times \ldots \times d_n$ specifying the payoffs of the game
  Outputs
    :List  
      the list of Spohn matrices $(M_1, \ldots , M_n)$ describing the dependency equilibria of the game $X$
  Description
    Text 
      The list $Di = \{d_1,\dots ,d_n \}$ represents the format of the game. It is crucial that the formats in PR and X match up.
      For $i=1,\ldots, n$ the Spohn matrix $M_i$ is the $d_i \times 2$ matrix describing the expected payoff of the $i$-th player.
      The Spohn matrices $M_1,\ldots , M_n$ have rank one at the dependency equilibria of the game $X$.
      
    Example
      Di = {2,2,3};
      PR = probabilityRing(Di);
      X = randomGame(Di);

      I = spohnMatrices(PR,X)

  SeeAlso
    probabilityRing
    randomGame
    spohnIdeal
    konstanzMatrix
    
///

------------------------------
-- Documentation spohnIdeal --
------------------------------

doc ///
  Key
    spohnIdeal
    
  Headline
    compute the ideal of the Spohn variety of a given game
  Usage
    spohnIdeal(PR,X)
  Inputs
     PR:Ring 
      a probability ring obtained via probabilityRing(Di), where $Di = \{ d_1, \ldots, d-n \}$ is the format of the game
     X:List 
      a list of n tensors of format $d_1 \times \ldots \times d_n$ specifying the payoffs of the game
  Outputs
    :List  
      the ideal generated by the $2\times 2$ minors of the Spohn matrices of the game $X$
  Description
    Text 
      The list $Di = \{d_1,\dots ,d_n \}$ represents the format of the game. It is crucial that the formats in PR and X match up.
      The Spohn ideal $I_X$ is the ideal defining the Spohn variety of a game $X$, which contains the dependency equilibria of the game $X$. Its generators are given by the $2\times 2$ minors of the Spohn matrices.
      This function uses the function spohnMatrices to compute the Spohn matrices of the given game.
      
    Example
      Di = {2,2,3};
      PR = probabilityRing(Di);
      X = randomGame(Di);

      I = spohnIdeal(PR,X)

  SeeAlso
    probabilityRing
    randomGame
    spohnMatrices
    konstanzMatrix
///

----------------------------------
-- Documentation konstanzMatrix --
----------------------------------

doc ///
  Key
    konstanzMatrix
    
  Headline
    constructs the Konstanz matrix of a given game
  Usage
    konstanzMatrix(PR, X)
  Inputs
    PR:Ring 
      a probability ring obtained via probabilityRing(Di), where $Di = \{ d_1, \ldots, d-n \}$ is the format of the game
    X:List 
      a list of n tensors of format $d_1 \times \ldots \times d_n$ specifying the payoffs of the game
  --Optional inputs
  --  KonstanzVariableName => ..., default value k, optional input to choose another variable name
  Outputs
    :Matrix  
      the $(d_1 + \ldots + d_n) \times (d-1 \cdots d_n)$-dimensional Konstanz matrix 
  Description
    Text 
      The list $Di = \{d_1,\dots ,d_n \}$ represents the format of the game. It is crucial that the formats in PR and X match up.
      The Konstanz matrix $K_X(k)$ is the unique matrix with monic polynomials as entries such that the Spohn variety is the union $\bigcup_{k \in (\mathbb P^1)^n} \ker K_X(k)$.
      
    Example
      Di = {2,2,3};
      PR = probabilityRing(Di);
      X = randomGame(Di);

      K = konstanzMatrix(PR,X)

    Text
     Indeed, then we can obtain the Spohn variety from the Konstanz matrix as described above.

    Example
      P = vector gens PR;
      R = QQ[apply(enumerateTensorIndices Di, j -> p_j), apply(#Di, i -> k_i)];
      I = substitute(eliminate({k_0,k_1,k_2},substitute(ideal entries(K*P), R)), PR);
      I == spohnIdeal(PR,X)

    Text
      The optional argument KonstanzVariableName allows to change the name of the variables. 
      If no variable name choice is specified, the variables will be named with k.
      
    Example
      Di = {2,2};
      PR = probabilityRing(Di);
      X = randomGame(Di);

      K = konstanzMatrix(PR,X, KonstanzVariableName => "z")

  SeeAlso
    probabilityRing
    randomGame
    spohnMatrices
    spohnIdeal
   
///



--******************************************--
-- TESTS     	       	    	      	    --
--******************************************--

-----------------------------------
--- TEST enumerateTensorIndices ---
-----------------------------------

TEST ///
assert(enumerateTensorIndices 3 === {{0}, {1}, {2}})
assert(enumerateTensorIndices {2,2} === {
    {0,0}, {0,1},
    {1,0}, {1,1}
})
assert(enumerateTensorIndices {2,1,2} === {
    {0,0,0}, {0,0,1},
    {1,0,0}, {1,0,1}
})
///

-----------------------
--- TEST zeroTensor ---
-----------------------

TEST ///
T = zeroTensor(QQ, {2,2})
assert(class T === Tensor)
assert(format T === {2,2})
assert(coefficientRing T === QQ)
assert(indexset T === {{0,0},{0,1},{1,0},{1,1}})
assert(all(select(keys T, k -> class k === List), k -> T#k == 0_QQ))
///

-------------------------
--- TEST randomTensor ---
-------------------------

TEST ///
T = randomTensor(QQ, {2,2})
assert(class T === Tensor)
assert(format T === {2,2})
assert(coefficientRing T === QQ)
assert(indexset T === {{0,0},{0,1},{1,0},{1,1}})
-- testing randomness is tricky.
///

------------------
--- TEST slice ---
------------------

TEST ///
T = zeroTensor(QQ, {2,3,2});
T#{0,0,0} = 5;
T#{0,1,0} = 6;
T#{0,2,0} = 7;
S = slice(T, {0}, {0});
assert(S === {5,6,7});
///

----------------------------------
--- TEST getVariableToIndexset ---
----------------------------------



----------------------------
--- TEST assemblePolynomial ---
----------------------------

---------------------------------------
--- TEST assemblePlayeriPolynomials ---
---------------------------------------



---------------------------------
--- TEST correlatedEquilibria ---
---------------------------------

TEST ///
X1 = randomTensor(QQ, {2,2,2})
X2 = randomTensor(QQ, {2,2,2})
X3 = randomTensor(QQ, {2,2,2})
CE = correlatedEquilibria {X1, X2, X3}
assert(class CE === Polyhedron)
assert(#vertices CE >= 1) -- CE polytope must be non-empty
///

---------------------------------
--- TEST correlatedEquilibria ---
---------------------------------

TEST ///
X1 = zeroTensor(QQ, {2,2});
X2 = zeroTensor(QQ, {2,2});
X0#{0,0} = -99; X0#{0,1} = 1; X0#{1,0} = 0; X0#{1,1} = 0;
X1#{0,0} = -99; X1#{0,1} = 0; X1#{1,0} = 1; X1#{1,1} = 0;
assert(class CE === Polyhedron)
assert(#vertices CE > ------
///

---------------------------
--- TEST probabilityRing---
---------------------------

TEST ///
Di = {2,2,2}
R = probabilityRing(Di, CoefficientRing=>QQ, ProbabilityVariableName=>"q")
Q = zeroTensor(Di)

Q#{0,0,0}=q#{0,0,0}
Q#{0,0,1}=q#{0,0,1}
Q#{0,1,0}=q#{0,1,0}
Q#{0,1,1}=q#{0,1,1}
Q#{1,0,0}=q#{1,0,0}
Q#{1,0,1}=q#{1,0,1}
Q#{1,1,0}=q#{1,1,0}
Q#{1,1,1}=q#{1,1,1}

assert(all for j in enumerateTensorIndices Di list Q#j === q#j)
///

-----------------------
--- TEST randomGame ---
-----------------------

TEST /// 
 Di = {2,2,3}
 X = randomGame(Di)
 assert(#X == #Di and all(#Di, i -> format(X#i) == Di))
/// 

--------------------------
--- TEST spohnMatrices ---
--------------------------

TEST /// 
 Di = {2,2,3};
 PR = probabilityRing(Di);
 X = randomGame(Di);
 M = spohnMatrices(PR,X)
/// 

-----------------------
--- TEST spohnIdeal ---
-----------------------

TEST /// 
 Di = {2,2,3};
 PR = probabilityRing(Di);
 X = randomGame(Di);
 I = spohnIdeal(PR,X)
 assert(I == sum(spohnMatrices(PR,X), m -> minors(2, m)) )
/// 

---------------------------
--- TEST konstanzMatrix ---
---------------------------

TEST /// 
 Di = {2,2,3};
 PR = probabilityRing(Di);
 X = randomGame(Di);
 K = konstanzMatrix(PR,X);
 P = vector gens PR;
 R = QQ[apply(enumerateTensorIndices Di, j -> p_j), apply(#Di, i -> k_i)];
 I = substitute(eliminate({k_0,k_1,k_2},substitute(ideal entries(K*P), R)), PR);
 assert(I == spohnIdeal(PR,X))
/// 


--------------------------------------
-- TEST toMarkovRing
--------------------------------------

TEST///
    R = probabilityRing({2,3,4}, CoefficientRing => ZZ/32003, ProbabilityVariableName => "x");
    markovR = toMarkovRing R;
    correctGens = {p_(1,1,1), p_(1,1,2), p_(1,1,3), p_(1,1,4), p_(1,2,1), p_(1,2,2),
      p_(1,2,3), p_(1,2,4), p_(1,3,1), p_(1,3,2), p_(1,3,3), p_(1,3,4),
      p_(2,1,1), p_(2,1,2), p_(2,1,3), p_(2,1,4), p_(2,2,1), p_(2,2,2),
      p_(2,2,3), p_(2,2,4), p_(2,3,1), p_(2,3,2), p_(2,3,3), p_(2,3,4)};
    assert(gens markovR === correctGens)
///


--------------------------------------
-- TEST mapToMarkovRing
--------------------------------------

TEST///
    R = probabilityRing({2,3,4}, CoefficientRing => ZZ/32003, ProbabilityVariableName => "x");
    markovR = toMarkovRing R;
    F = mapToMarkovRing R;
    assert(target F === markovR)
    assert(source F === R)
    assert(isInjective F === true)
///


--------------------------------------
-- TEST mapToProbabilityRing
--------------------------------------

TEST///
    R = probabilityRing({2,3,4}, CoefficientRing => ZZ/32003, ProbabilityVariableName => "x");
    markovR = toMarkovRing R;
    F = mapToMarkovRing R;
    assert(target F == R)
    assert(source F == markovR)
    assert(isInjective F == true)
///

--------------------------------------
-- TEST ciIdeal
--------------------------------------

TEST///
     FF = ZZ/32003
     PR = probabilityRing(d, CoefficientRing => FF);
     G1 = graph ({{1,2},{2,3},{1,3}});
     G2 = graph ({}, Singletons => {1,2,3});
     I1 = ciIdeal(PR, G1);
     I2 = ciIdeal(PR, G2);
     assert(I1_0==0)
     assert(numcols mingens I2 == 9)
///

TEST///
     FF = ZZ/32003
     PR = probabilityRing(d, CoefficientRing => FF);
     G = graph ({{1,2},{2,3}});
     I = ciIdeal(PR, G);
     assert(I==ideal(-p_{0, 0, 1}*p_{1, 0, 0}+p_{0, 0, 0}*p_{1, 0, 1},-p_{0, 1, 1}*p_{1, 1, 0}+p_{0, 1, 0}*p_{1, 1, 1}))
///

--------------------------------------
-- TEST intersectWithCImodel
--------------------------------------

TEST///
     FF = ZZ/32003
     d = {2,3,2};
     X = randomGame(d, CoefficientRing => FF);
     PR = probabilityRing(d, CoefficientRing => FF);
     G = graph ({{1,2}},Singletons => {3});
     L={{{1,2},{3},{}}};
     V = spohnIdeal(PR, X);
     I1 = intersectWithCImodel(V, L);
     I2 = intersectWithCImodel(V, G);
     assert(I1==I2)
     assert(numcols mingens I1 == 20)
///

TEST///
     FF = ZZ/32003
     d = {2,2,2};
     X = randomGame(d, CoefficientRing => FF);
     PR = probabilityRing(d, CoefficientRing => FF);
     G = graph ({{1,2},{2,3},{1,3}});
     V = spohnIdeal(PR, X);
     I = intersectWithCImodel(V, G);
     assert(V==I)
///

--------------------------------------
-- TEST spohnCI
--------------------------------------

TEST///
     FF = ZZ/32003
     d = {2,3,2};
     X = randomGame(d, CoefficientRing => FF);
     PR = probabilityRing(d, CoefficientRing => FF);
     G = graph ({{1,2}},Singletons => {3});
     L={{{1,2},{3},{}}};
     V = spohnIdeal(PR, X);
     I1 = spohnCI(PR, X, L);
     I2 = spohnCI(PR, X, G);
     assert(I1==I2)
///

TEST///
     FF = ZZ/32003
     d = {2,2,2};
     X = randomGame(d, CoefficientRing => FF);
     PR = probabilityRing(d, CoefficientRing => FF);
     V = spohnIdeal(PR, X);
     G = graph ({{1,2},{2,3}});
     I = spohnCI(PR, X, G);
     assert(numcols mingens I==8))
///

TEST///
     FF = ZZ/32003
     d = {2,2,2};
     X = randomGame(d, CoefficientRing => FF);
     PR = probabilityRing(d, CoefficientRing => FF);
     G = graph ({{1,2},{2,3},{1,3}});
     V = spohnIdeal(PR, X);
     I = spohnCI(PR, X, G);
     assert(V==I)
///
