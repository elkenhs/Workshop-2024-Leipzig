needsPackage "GameTheory"

probabilityRing = method(Options => { CoefficientRing => QQ, ProbabilityVariableName => "p" })
probabilityRing List := Ring => opts -> Di -> (
    J := enumerateTensorIndices Di;
    p := getSymbol opts.ProbabilityVariableName;
    K := opts.CoefficientRing;
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

genericProbabilityRing = method(Options => { CoefficientRing => QQ, ProbabilityVariableName => "p", PayoffVariableName => "x" })
genericProbabilityRing List := Ring => opts -> Di -> (
    J := enumerateTensorIndices Di;
    p := getSymbol opts.ProbabilityVariableName;
    x := getSymbol opts.PayoffVariableName;
    K := opts.CoefficientRing;

    L := toList(0 .. (#Di - 1));
    E := L ** J;
    R := K[apply(E, e -> x_e), apply(J, j -> p_j)];

    P := zeroTensor(R, Di);
    for j in J do P#j = (p_j)_R;
    R#"probabilityVariable" = P;

    X := apply(#Di, i -> zeroTensor(R, Di));
    for i to #Di-1 do
        for j in J do X_i#j = x_(i, j)_R;
    R#"payoffVariable" = X;

    R#"gameFormat" = Di;
    R)


-------------------------------
--Documentation----------------
-------------------------------

-- probabilityRing

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

--randomGame

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
     Outputs of this function can be used as input for the functions spohnMatrices, spohnIdeal and konstanzMatrix. 

  SeeAlso
    spohnMatrices
    spohnIdeal
    konstanzMatrix
///

--spohnMatrices

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

--spohnIdeal

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

--konstanzMatrix

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

-- genericProbabilityRing (possibly leave this out)
doc ///
    Key
        genericProbabilityRing
        (genericProbabilityRing, List)
    Headline
        Ring of probability distributions of a game indexed by ordered multi-indices, with an additional variable representing the generic payoffs of a game.
    Usage
        genericProbabilityRing(Di)
    Inputs
        Di:List
           a list of natural numbers $d_0,\dots,d_{n-1}$
    -- Optional inputs
    --     CoefficientRing => ..., default value QQ, optional input to choose the base field
    --     ProbabilityVariableName => ..., default value "p", symbol used for the tensor of probability variables
    --     PayoffVariableName => ..., default value "x", symbol used for the tensors of payoff variables
    Outputs
        :Ring  
         a polynomial ring with a tensor of variables $p_{i_0,\dots,i_{n-1}}$
         and for each player $a=0,\dots,n-1$ a tensor of variables $x^a{i_0,\dots,i_{n-1}}$,
         where $i_j$ runs from $0$ to $d_j-1$.
    Description
        Text
            The list $Di$ represents the format of the game.
            In this example we create a ring of probability distributions coming from a
            game with format {2, 3, 2}. This format can be accessed from the ring through
            the field "gameFormat".
            
            The variables $p#i$ are the entries of the tensor $p$, which can be
            accessed from the ring through the field "probabilityVariable".

            The tensor $x_i$ represents the generic payoff tensor of player $i$, and
            can be accessed from the ring through the field "payoffVariable".

        Example
            Di = {2,1,2};
            GPR = genericProbabilityRing Di;
            numgens GPR
            pairs GPR#"probabilityVariable"
            pairs GPR#"payoffVariable"_1
      
        Text 
            The optional argument "CoefficientRing" allows to change the base field. If no choice is
            specified, the base field is set to QQ. It is also possible to change the name of the
            variable tensor through the optional argument "ProbabilityVariableName", which is set to
            the string "p" by default, and the name of the payoff tensor through the optional argument "PayoffVariableName",
            which is set to the string "x" by default.
 
        Example
            GPR2 = genericProbabilityRing(Di, Coefficients=>RR, ProbabilityVariableName=>q, PayoffVariable=>y);
            coefficientRing GPR2
            pairs GPR2#"probabilityVariable"
            pairs GPR2#"payoffVariable"_1
      
        -- Figure out all of the functions which require a probabilityRing
        Text
            -- The functions @TO genericGame@ ... require the ring to be created by this function
            -- or in a similar manner.
///



---------------------------------
--Tests--------------------------
---------------------------------

-- probabilityRing

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

--randomGame

TEST /// 
 Di = {2,2,3}
 X = randomGame(Di)
 assert(#X == #Di and all(#Di, i -> format(X#i) == Di))
/// 

--spohnMatrices

TEST /// 
 Di = {2,2,3};
 PR = probabilityRing(Di);
 X = randomGame(Di);
 M = spohnMatrices(PR,X)
/// 

--spohnIdeal

TEST /// 
 Di = {2,2,3};
 PR = probabilityRing(Di);
 X = randomGame(Di);
 I = spohnIdeal(PR,X)
 assert(I == sum(spohnMatrices(PR,X), m -> minors(2, m)) )
/// 


--konstanzMatrix

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

-- genericProbabilityRing (possibly leave this out)

TEST ///
Di = {2,2,2}
R = genericProbabilityRing(Di, CoefficientRing=>QQ, ProbabilityVariableName=>"q", PayoffVariableName=>"y")
Q = zeroTensor(Di)
Y = {zeroTensor(Di), zeroTensor(Di), zeroTensor(Di)}

Q#{0,0,0}=q#{0,0,0}
Q#{0,0,1}=q#{0,0,1}
Q#{0,1,0}=q#{0,1,0}
Q#{0,1,1}=q#{0,1,1}
Q#{1,0,0}=q#{1,0,0}
Q#{1,0,1}=q#{1,0,1}
Q#{1,1,0}=q#{1,1,0}
Q#{1,1,1}=q#{1,1,1}

Y_0#{0,0,0}=y_(0, {0,0,0})
Y_0#{0,0,1}=y_(0, {0,0,1})
Y_0#{0,1,0}=y_(0, {0,1,0})
Y_0#{0,1,1}=y_(0, {0,1,1})
Y_0#{1,0,0}=y_(0, {1,0,0})
Y_0#{1,0,1}=y_(0, {1,0,1})
Y_0#{1,1,0}=y_(0, {1,1,0})
Y_0#{1,1,1}=y_(0, {1,1,1})

Y_1#{0,0,0}=y_(1, {0,0,0})
Y_1#{0,0,1}=y_(1, {0,0,1})
Y_1#{0,1,0}=y_(1, {0,1,0})
Y_1#{0,1,1}=y_(1, {0,1,1})
Y_1#{1,0,0}=y_(1, {1,0,0})
Y_1#{1,0,1}=y_(1, {1,0,1})
Y_1#{1,1,0}=y_(1, {1,1,0})
Y_1#{1,1,1}=y_(1, {1,1,1})

Y_2#{0,0,0}=y_(2, {0,0,0})
Y_2#{0,0,1}=y_(2, {0,0,1})
Y_2#{0,1,0}=y_(2, {0,1,0})
Y_2#{0,1,1}=y_(2, {0,1,1})
Y_2#{1,0,0}=y_(2, {1,0,0})
Y_2#{1,0,1}=y_(2, {1,0,1})
Y_2#{1,1,0}=y_(2, {1,1,0})
Y_2#{1,1,1}=y_(2, {1,1,1})

assert(all for j in enumerateTensorIndices Di list Q#j === q#j)
assert(all flatten for i from 0 to 2 list for j in enumerateTensorIndices Di list Y_i#j === y_(i,j))
///
