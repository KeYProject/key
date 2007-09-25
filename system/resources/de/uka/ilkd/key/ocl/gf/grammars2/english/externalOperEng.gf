--# -path=.:../prelude:../resourceAbstract:../resourceEnglish:../resource

--1 API for User-Defined Entities.
--
-- This file contains opers for translating constraints, classes, attributes, 
-- assocations and operations in to English.
-- The user defined english grammars should use these opers when linearizing 
-- the user defined UML types.
-- The English OCL library should also use these opers when linearizing OCL types.

resource externalOperEng = open 
    Prelude,
    AtomEng, ResourceEng, TypesEng,ParadigmsEng, PredicationEng,
    formatOCL,  internalOperEng,   myTypesEng, myResourceExtEng, PropsAndPredsEng in {

 
--!
--2 Opers used for constructing Classes
-- Used for creating classes of type ClassL.
-- Classes consist of two parts.
-- The first part is a common noun phrase (CN) and corresponds to the 
-- "class name", which is what is used when translating the class into 
-- English in a regular sentence.
-- The second field is a string, "classId", and is the actual name of the class.
-- This is used when formally specifying the class name.
--    
-- The main oper to be used when constructing classes is $mkClass$.
-- A second class building oper, $mkCollClass$ can be used when making
-- collections classes.
-- There are also several opers in this API that can be used to create the 
-- CN that must be specified when using $mkClass$. Alternatively, the resource
-- grammars can also be used to create the desired CN.
--
-- Examples: 
--* $mkClass (adjCN "owner" (strCN "PIN")) "OwnerPIN"$ is translate to "the owner PIN"
--* $mkClass (exceptionCN "user")) "UserException"$ is translated to "the user exception"
--* $mkClass (classCN "utility")) "Util"$ is translated to "the utility class"
--* $mkCollClass setN "Set" IntegerC$ is translated to "the set of Integers"

oper  		

-- Standard oper. CN represents the natural language representation for the class.
-- Str represents the classId, which is the official name of the class.
  mkClass : CN -> Str -> ClassL; 
  		
-- Used for OCL collection types such as Set, Bag etc.
-- E.g. $mkCollClass setNoun "Set" IntegerClass$ -
-- gives a natural language representation = "set of integers", 
-- and a classId = Set (Integer)
  mkCollClass : N -> Str -> ClassL -> ClassL;



--!
--2 Opers for creating properties.
-- Attributes, operations and associations can be considered to be 
-- properties of the objects they belong to. They share many characteristics
-- and are often linearized in a similar manner. For this reason, we have not
-- based the linearization style on a separation between attributes, operations
-- and associations. Instead, we have separated linearization according to
-- the different types of property that exist.
--
-- Properties are generally either a common noun phrase (CN) or an 
-- adjective phrase (AP).
-- The various types of CN or AP can be constructed using the opers found in
-- this API, or by using opers from the resource grammars.
-- Once a CN/AP is constructed, it should be converted into a property
-- using one of the various $mkXXXProperty$ opers.
--
-- When properties are linearized, they get linearized in one of two ways.
-- Either the object that they belong to is mentioned, or it is implicit.
-- In $core.gf$ funs are defined for linearizing the properties.
-- These funs are of the form $useXXXProperty$ and $useXXXPropertyImplicit$.
--
-- In some cases it is obvious which property to use for an 
-- attribute/operation/association.
-- In other cases, several property types would work and then it becomes a user
-- choice about which is most suitable.
-- Each property type is explained below.
--
-- $SimpleProperty$ is linearized as "the property of the object", or 
-- when the implicit form is used, "the property".
-- This is used for many attributes, 
-- e.g. "the try counter of the owner PIN",
-- associations, e.g. "the private key of the key pair"
-- and 'get' operations, e.g. $JCSystem.getTransactionDepth()$ becomes
-- "the transaction depth of the Java Card System".
   
    mkSimpleProperty : CN -> PropertyL;
    

-- $IsPredicate$ is linearized as "the object is/is not property", where
-- property is an AP. The implicit form is treated in the same way.
-- This is used for 'is' attributes and operations.
-- e.g. $OwnerPIN.isValidated()$ is translated to
-- "the owner PIN is validated".
    
    mkIsPredicate : AP -> PredicateL;


-- When building a predicate from a string 
-- the linearization is "the property holds for the object", or 
-- when the implicit form is used, "the property holds".
-- This is used for boolean attributes and operations that return booleans,
-- but that are not $IsPredicate$'s
-- E.g. "the property" $check$ "on the owner PIN is true"

    mkStrPredicate : Str -> PredicateL;


-- $OnProperty$ is linearized as "the property on the object", or 
-- when the implicit form is used, "the property".
-- This is used mainly when operations are used in their literal form.
-- e.g. $Util.mkShort(x1, x2)$ translates to
-- "the query" $mkShort(x1, x2)$ "on the Utility class"

    mkOnProperty : CN -> PropertyL;

        
-- $StaticProperty$ is linearized as "the property (specified in object)", 
-- or when the implicit form is used, "the property".
-- This can be used for properties when there is a complex piece of text 
-- representing an attribute, assocation or an operation, 
-- that should not be combined with the object name in the conventional way.
-- e.g. $Util.mkShort(x1, x2)$ could be translated to
-- "the short value concatenation of x1 and x2 (specified in Util)"        

    mkStaticProperty : CN -> PropertyL;

    
-- $AssocProperty$ is linearized as 
-- "the set of property associated with the object",
-- or when the implicit form is used, "the set of property".
-- This can be used for many associations that have a multiplicity of greater
-- than one.
-- e.g. "the set of authors associated with the paper"

    mkAssocProperty : CN -> PropertyL;
	

--!
--2 Grammar building opers
-- Classes and properties are generally built from common noun phrases (CN) 
-- or adjective phrases (AP).
-- The opers below can be used to construct various types of CN or AP.
-- Once a CN/AP is constructed, it can then be converted into a class or
-- property as appropriate.
--    
-- E.g. For the attribute $transactionDepth$, we want to have the translation
-- "the transaction depth". We can do this using the following:
--
-- $mkSimpleProperty (adjCN "transaction" (strCN "depth"))$
--

--3 Opers for creating common noun phrases.


-- Create a CN from a string
  strCN : Str -> CN;

-- Create a CN from a N
  nCN : N -> CN;              	


-- Modify the CN with an adjective.
-- This can be used when constructing classes or properties whose names consist
-- of more than one word.
-- E.g. $adjCN "private" (strCN "key")$ produces the CN "the private key".
  adjCN : Str -> CN -> CN;
    
    
-- For standard exception classes: Produces "<name> exception"
-- E.g. $exceptionCN "user"$ results in "user exception"
  exceptionCN : Str -> CN;

-- Appends the word class after the CN.
-- E.g. $classCN "utility"$ results in "utility class"
  classCN : Str -> CN;

     	    
-- Appends the word attribute after the CN.    
-- E.g. "the triesLeft attribute"
  attrCN : Str -> CN;

	    
-- Appends the word attribute after the name of the property.
-- Also contains an embedded note that is displayed when possible.
-- When HTML formatting is used, the note is displayed as a tooltip.
-- When LaTeX formatting is used, the note is displayed as a footnote. 
  attrNoteCN : Str -> S -> CN;


-- This deals with properties of the form "x of y". E.g. 'maxTries'.
-- E.g.
-- $ofCN (adjCN "maximum" (strCN "number")) (strCN "tries")$
-- Translates to "maximum number of tries"
  ofCN : CN -> CN -> CN;

     	
-- This is for dealing with 'constants'. The string is the name of the
-- constant. The CN is the type of constant.
-- E.g. $constCN "FULL-INCOMING" (strCN "state")$,
-- gets translated as "the FULL-INCOMING state".
-- Furthermore, the name of the constant gets printed in a 'code' font.
  constCN : Str -> CN -> CN;


-- This is for dealing with boolean attributes that are not 'is' attributes.
-- E.g. $propertyCN "initialised"$,
-- gets translated as "property initialised".
-- If this is then used as a $BooleanProperty$, we get the text
-- "the property initialised is true"
  propertyCN : Str -> CN;
         
-- Translates to "the query <query-name> (args)"    
  queryCN : Str -> ArgList -> CN;
    
-- Translates to "the query <query-name> (args)".
-- Also contains an embedded note that is displayed when possible.
-- When HTML formatting is used, the note is displayed as a tooltip.
-- When LaTeX formatting is used, the note is displayed as a footnote. 
  queryNoteCN : Str -> ArgList -> S -> CN;
	        
-- Modify the CN with some text. This can be used when creating complex
-- CNs for use with $StaticProperty$. See $argCN$ for an example.
  textCN : CN -> Str -> CN;

        
-- Add an argument to the CN. This can be used when creating complex
-- CNs for use with $StaticProperty$. Some operations need to be described
-- with a complex text that uses the arguments of the operation.
-- E.g. $makeShort(x1, x2)$ could be translated as 
-- "the short value concatenation of x1 and x2", by using the following
-- construction: $mkStaticProperty (argCN (textCN (argCN (textCN (textCN (textCN (textCN (strCN "short") "value") "concatenation") "of") x1) "and") x2);
-- This is not a grammatically correct way of constructing this.
-- Ideally the resource grammars should be used.
-- This is a temporary solution to allow automated production of complex text
-- until a better solution is found.
  argCN : CN -> Inst -> CN;


-- Combine an adjective phrase with a CN. E.g. "the EC SVDP DH algorithm", "the OUTGOING state"
-- etc.
  apCN : AP -> CN -> CN;
  
	    
--3 Opers for creating adjective phrases.


-- Create a adjective phrase from a string
  strAP : Str -> AP;

            	
-- Build up the AP by adding another adj before it.    
  adjAP : Str -> AP -> AP;
    
    
-- Create an AP from an adjective
  adj1AP : Adj1 -> AP;


--3 Opers for creating sentences	    
-- This oper allows sentences to be constructed from strings.
-- This is not correct grammatically, but is just a 'quick' solution to allow
-- sententeces to be built automatically for
-- use when adding notes to attributes/operations.
-- Ideally, the resource grammars should be used for constructing sentences.
  mkSent : Str -> S;


--3 Opers for creating arguments for operations
-- Some query building opers expect an ArgList.
-- These opers allow arbitrarily long arg lists to be built.
    
    argNil : ArgList;
    argCons : Inst -> ArgList -> ArgList;
	


--!
--2 Opers for building constraints
-- Used for linearizing constraints. Classes, attributes, operations and 
-- associations are used when specifying OCL constraints. Many OCL keywords
-- and constructs are also used.
-- When all these are linearized, they need to be tied together into text
-- that shows what invariants, pre-conditions and post-conditions belong to
-- what class or operation. This text varies for class invariants, operations
-- of classes and constructors of classes.
-- The opers below can be used for building the various constraint texts.
--
    

-- Used for operations with no parameters and no return type.
  contextOp00 : Str -> Str -> OperConstraintBodyL -> ConstraintL;

-- Used for operations that have parameters but no return type.
  contextOp10 : (class, op, args : Str) -> OperConstraintBodyL -> ConstraintL;

-- Used for operations with no parameters but that have a return type.
  contextOp01 : (class, op, ret : Str) -> OperConstraintBodyL -> ConstraintL;

-- Used for operations with both parameters and return type.
  contextOp11 : (class, op, args, ret : Str) -> OperConstraintBodyL -> ConstraintL;

-- Used for constructors with no parameters
  contextCon0 : Str -> Str -> OperConstraintBodyL -> ConstraintL;
		
-- Used for constructors that have parameters
  contextCon1 : (class, op, args : Str) -> OperConstraintBodyL -> ConstraintL;
		
-- Use for class invariants
  contextClass : Str -> ClassConstraintBodyL -> ConstraintL;
  
  
--!
-- Enumerations

    mkEnum : Str -> ClassL;
    enumVal : Str -> Inst;

-- The definitions should not bother the user of the API. So they are
-- hidden from the document.
--.
        
    mkClass = \classname, classId -> classname ** {s42 = classId};
    mkCollClass = \collection, Collection, IntegerC -> 
        (AppFun (funOfCN (UseN collection)) 
        (IndefManyNP (class2cn IntegerC))) ** {s42 = Collection ++ "(" ++ (class2id IntegerC) ++ ")"};

    mkEnum = \ident -> UseN (nNonhuman ident) ** {s42 = ident};
        
    mkSimpleProperty = PropsAndPredsEng.mkSimpleProperty; --\prop -> prop;    
    mkIsPredicate = PropsAndPredsEng.mkIsPredicate; -- \prop -> prop;
    mkStrPredicate = PropsAndPredsEng.mkStrPredicate; --\prop -> prop;
    mkOnProperty = PropsAndPredsEng.mkOnProperty; -- \prop -> prop;
    mkStaticProperty = PropsAndPredsEng.mkStaticProperty; --\prop -> prop;
    mkAssocProperty = PropsAndPredsEng.mkAssocProperty; --\prop -> prop;
	
	
    strCN = \prop -> UseN (nNonhuman prop);
    nCN = \prop -> UseN prop;                	
    adjCN = \adj, prop -> (ModAdj (AdjP1 (mkAdj1 adj)) prop);
        
    exceptionCN = \classname -> adjCN classname (UseN exceptionN);
    classCN = \classname -> adjCN classname (UseN classN);
    attrCN = \attr -> (ModAdj (AdjP1 (mkAdj1 (mkCode attr))) (UseN attributeN));
    attrNoteCN = \attr, note ->
        (ModAdj (AdjP1 (mkAdj1 (mkNote attr note.s))) (UseN attributeN));
    ofCN = \prop1, prop2 -> appFam1 (funOfCN prop1) (MassNP prop2);
    constCN = \attr, type -> apCN (strAP (mkCode attr)) type;
    propertyCN = \prop -> (ModAdj propertyAP (strCN prop));
    queryCN = \query, args -> 
        nameCN (UseN queryN) (mkCode (query ++ "(" ++ args.s ++ ")"));
    queryNoteCN = \query, args, note -> 
        nameCN (UseN queryN) (mkNote (query ++ "(" ++ args.s ++ ")") note.s);
    textCN = \prop, text -> nameCN prop text;
    argCN = \prop, arg -> nameCN prop (inst2str arg);
    apCN = \ap, cn -> ModAdj ap cn;
    
    strAP = \adj -> AdjP1 (mkAdj1 adj);	        
    adjAP = \str, prop -> AdvAP (mkAdA str) prop;
    adj1AP = \adj -> AdjP1 adj;

    mkSent = \str -> {s = str; lock_S = <>};
    
    argNil = {s = ""; empty = True};
    argCons = \x, xs -> {s = case xs.empty of {
		True => (inst2np x).s!NomP;
		False => xs.s ++ "," ++ (inst2np x).s!NomP
	}; empty = False};
	

  contextOp00 = \class, op, body -> 
    (AdVS (opAdV operationN op class) (operCB2s body));

  contextOp10 = \class, op, args, body -> 
    (AdVS (opAdV operationN (op ++ "(" ++ args ++ ")") class) 
    (operCB2s body));

  contextOp01 = \class, op, ret, body -> 
    (AdVS (opAdV operationN (op ++ "()" ++ ":" ++ ret) class) 
    (operCB2s body));

  contextOp11 = \class, op, args, ret, body -> 
    (AdVS (opAdV operationN (op ++ "(" ++ args ++ ")" ++ ":" ++ ret) class) 
    (operCB2s body));

  contextCon0 = \class, op, body -> 
    (AdVS (opAdV constructorN op class) (operCB2s body));

  contextCon1 = \class, op, args, body -> 
    (AdVS (opAdV constructorN (op ++ "(" ++ args ++ ")") class) 
    (operCB2s body));
	
  contextClass = \class, body -> (AdVS (classAdV classN class)(classCB2s body));
  
  enumVal str = constNoInfl (mkCode str);

}
