--# -path=.:../prelude:../abstract
concrete oclLibraryOCL of oclLibrary = coreOCL ** open Prelude, externalOperOCL, precedenceOCL in {



lin	sent2bool s = s;
lin	bool2sent b = b;

printname sent2bool = ["use a sentence as a boolean\\%BOOL{boolean operators}"];
printname bool2sent = ["use a boolean as a sentence\\%BOOL"];


--
-- 'ideomatic expressions', recurring patterns in OCL specs:
--
lin decremented exp decr = {
        s0 = (
            infix eqP "=" 
            exp
            (infix addP "-" 
                (mkAtPre exp)
                decr)
        ).s0;
        s1 = ["*** NOT ALLOWED ***"]; -- no atPre for this construction
        isAtpre = False;
        p = eqP
    };

    incremented exp decr = {
        s0 = (
            infix eqP "=" 
            exp
            (infix addP "+" 
                (mkAtPre exp)
                decr)
        ).s0;
        s1 = ["*** NOT ALLOWED ***"]; -- no atPre for this construction
        isAtpre = False;
        p = eqP
    };

    notChanged _ exp = {
        s0 = (infix eqP "=" exp (mkAtPre exp)).s0;
        s1 = ["*** NOT ALLOWED ***"]; -- no atPre for this construction
        isAtpre = False; p = eqP
    };


--
-- KeY extensions
--
lin
	NullC = stdClass "Null";
	nullConforms2 c = ss (["Null conforms to"] ++ c.s);
	null = const "null";
	excThrown _ a e = dotOper1 a "excThrown" e;

printname
	NullC 		= ["Null"]
		++ ["\\$The class of null or nil value which stands for undefined.<br>Is not an official part of OCL."]
		++ ["\\%PREDEF{predefined types of OCL}"];
	nullConforms2 	= ["Null as a subtype of everything"]
		++ ["\\%OCL"];
	null 		= ["Null"]
		++ ["\\$The null or nil value which stands for undefined.<br>Is not an official part of OCL."]
		++ ["\\%OCL"];
	excThrown 	= ["thrown exception"]
		++ ["To state that an exception will be thrown.<br>Is not an official part of OCL."]
		++ ["\\%OCL"];

--
-- OclType
--
lin
	OclTypeC 		= stdClass "OclType";
	OclTypeCConforms2OclTypeC = ss ["OclType conforms to OclType"];
	class2oclType c 	= const c.s;
	class2name c 		= const c.s;
	otName t 		= dotOper0 t "name";
	otAttributes t 		= dotOper0 t "attributes";
	otOperations t 		= dotOper0 t "operations";
	otSupertypes t 		= dotOper0 t "supertypes";
	otAllSupertypes t 	= dotOper0 t "allSupertypes";
	otAllInstancesStrict _ t = dotOper0 t "allInstances";

printname
	OclTypeC	= ["OclType"]
		++ ["\\$All types defined in a UML model, or pre-defined within OCL, have a type. This type is an instance of the OCL type called OclType."]
		++ ["\\%PREDEF"];
	OclTypeCConforms2OclTypeC = ["OclType\\$OclType as a subtype of itself"];
	class2oclType		= ["use a class as a OclType"]
		++ ["\\%OCL"]
		++ ["\\#class The class which should be used as an OclType"];
	class2name		= ["use classname from class"]
		++ ["\\%OCL"]
		++ ["\\#class The class which should be used as an OclType<br>TODO: difference to class2oclType?"];
	otName			= ["type.name"]
		++ ["\\$Results in the name of <i>type<i> as a String."]
		++ ["\\%OCL"]
		++ ["\\#type The OclType whose name is to be returned as a String."];
	otAttributes 		= ["type.attributes()"]
		++ ["\\$The set of names of the attributes of <i>type</>, as they are defined in the model."]
		++ ["\\%OCL"]
		++ ["\\#type The OclType"];
	otOperations 	 	= ["type.operations()"]
		++ ["\\$The set of names of the operations of <i>type</>, as they are defined in the model."]
		++ ["\\%OCL"]
		++ ["\\#type The OclType"];
	otSupertypes 		= ["type.supertypes()"]
		++ ["\\$The set of all direct supertypes of <i>type</i>."]
		++ ["\\%OCL"]
		++ ["\\#type The OclType"];
	otAllSupertypes 	= ["type.allSupertypes()"]
		++ ["\\$The transitive closure of the set of all supertypes of <i>type</i>."]
		++ ["\\%OCL"]
		++ ["\\#type The OclType"];
	otAllInstancesStrict 	= ["type.allInstanes()"]
		++ ["\\$The set of all instances of <i>type</i>and all its subtypes in existence at the snapshot at the time that the expression is evaluated."]
		++ ["\\%OCL"]
		++ ["\\#type The OclType"];


--
-- OclAny 
--
lin
	OclAnyC = stdClass "OclAny";
	conforms2OclAny c = ss (c.s ++ ["conforms to OclAny"]);
	anyOclIsKindOf a t = dotOper1 a "oclIsKindOf" t;
	anyOclIsTypeOf a t = dotOper1 a "oclIsTypeOf" t;
	anyOclAsTypeStrict c a t = dotOper1 a "oclAsType" t;
	anyOclInState a s = dotOper1 a "oclIsInState" s;
	anyOclIsNew a = dotOper0 a "oclIsNew";

printname
	OclAnyC		= ["OclAny\\$The supertype of every non-collection type in OCL"]
		++ ["\\%PREDEF"];
	conforms2OclAny	= ["every non-collection type is subtype of OclAny"];
	anyOclIsKindOf 	= ["object is kind of a type"]
		++ ["\\$True if <i>type</i> is one of the types of <i>object</i>, or one of the supertypes (transitive) of the types of <i>object</i> in <br><pre>object.oclIsKindOf(type : OclType)</pre>"]
		++ ["\\%OCL{OCL states and types}"]
		++ ["\\#!object The object whose type is of interest"]
		++ ["\\#type The OclType that <i>object</i> should have"];
	anyOclIsTypeOf 	= ["object has a destinctive type"]
		++ ["\\$True if <i>type</i> is equal to one of the types of <i>object</i>, in <br><pre>object.oclIsTypeOf(type : OclType)</pre>"]
		++ ["\\%OCL"]
		++ ["\\#!object The object whose type is of interest"]
		++ ["\\#type The OclType that <i>object</i> should have"];
	anyOclAsTypeStrict 	= ["explicit downcast"]
		++ ["\\$Results the same objects, but with the given type. If the cast fails, null is returned."]
		++ ["\\%OCL"]
		++ ["\\#targetType The type the casted <i>object</i> should have. Only downcasts are possible that way, upcasts result in undefined"]
		++ ["\\#object The object, that should be casted"]
		++ ["\\#OclType The OclType, that <i>object</i> should become. <br> Note: Will be used for the linearization, but does not affect the type, that is soley chosen by <i>targetType</i>!"];
	anyOclInState 	= ["object is in a specific OclState"]
		++ ["\\$Results in true if object is in the state state, otherwise results in false."]
		++ ["\\%OCL"]
		++ ["\\#state The name of a state in the state machine corresponding to the class of object."];
	anyOclIsNew 	= ["object is new"]
		++ ["\\$Evaluates to true if the object is created during performing the operation. That is, it didn't exist at precondition time.<br>Can only be used in a postcondition."]
		++ ["\\%OCL"]
		++ ["\\#!object The object that should be new"];
--
-- OclState 
--
lin 
	OclStateC 	= stdClass "OclState";
	OclStateCConforms2OclStateC = ss ["OclState conforms to OclState"];
printname 
	OclStateC	= ["OclState"]
		++ ["\\$The name of a state that appears in a statemachine."]
		++ ["\\%PREDEF"];
	OclStateCConforms2OclStateC = ["OclState"];




--
-- Integer
--
lin IntegerC = stdClass "Integer";
lin	
--	intEq a b = infix eqP "=" a b;
	intAdd a b = infix addP "+" a b;
	intSub a b = infixL addP "-" a b;
	intUnaryMinus a = prefix unP "-" a;
	intTimes a b = infix multP "*" a b;
	intDiv2Real a b = infixL multP "/" a b;
	intAbs a = dotOper0 a "abs";
	intDiv2Int a b = dotOper1 a "div" b;
	intMod a b = dotOper1 a "mod" b;
	intMax a b = dotOper1 a "max" b;
	intMin a b = dotOper1 a "min" b;

	oneSum a b = infix addP "+" a b;
	consSum t a = infix addP "+" t a;
	sumList2Integer a = a;
	
	oneProduct a b = infix multP "*" a b;
	consProduct t a = infix multP "*" t a;
	productList2Integer a = a;


printname
	IntegerC	= ["Integer\\$<html>integer or whole numbers<br>In OCL they are infinite like in mathematics.</html>\\%PREDEF"];
	intAdd 		= ["+ for integers\\$<html>int<sub>1</sub> + int<sub>2</sub></html>\\%ARITH{arithmetic operations}"];
	intSub 		= ["- for integers\\$<html>int<sub>1</sub> - int<sub>2</sub></html>\\%ARITH"];
	intUnaryMinus 	= ["unary minus for integers\\$<html>-int<sub>1</sub></html>\\%ARITH"];
	intTimes 	= ["* for integers\\$<html>int<sub>1</sub> * int<sub>2</sub></html>\\%ARITH"];
	intDiv2Real 	= ["/ for integers with real result\\$<html>int<sub>1</sub> / int<sub>2</sub></html>\\%ARITH"];
	intAbs 		= ["absolute value of an integer\\$<html>|int<sub>1</sub>|</html>\\%ARITH"];
	intDiv2Int 	= ["/ for integers with integer result\\$<html>[int<sub>1</sub> / int<sub>2</sub>]</html>\\%ARITH"];
	intMod 		= ["modulo for integers\\$<html>int<sub>1</sub> mod int<sub>2</sub></html>\\%ARITH"];
	intMax 		= ["maximum of two integers\\$<html><i>max</i>(int<sub>1</sub>, int<sub>2</sub>)<br>in OCL: int<sub>1</sub>.max(int<sub>2</sub>)</html>\\%ARITH"];
	intMin 		= ["minimum of two integers\\$<html><i>min</i>(int<sub>1</sub>, int<sub>2</sub>)<br>in OCL: int<sub>1</sub>.min(int<sub>2</sub>)</html>\\%ARITH"];

	oneSum		= ["close a sum list with a final sum\\$this refinement takes two Integers as arguments and no lists\\%ARITH"];
	consSum		= ["start a sum list\\$this refinement takes an Integer and a sum list as arguments\\%ARITH"];
	sumList2Integer	= ["use a sum list as an Integer\\%ARITH"];
	
	oneProduct		= ["close a product list with a final product\\$this refinement takes two Integers as arguments and no lists\\%ARITH"];
	consProduct		= ["start a product list\\$this refinement takes an Integer and a product list as arguments\\%ARITH"];
	productList2Integer	= ["use a product list as an Integer\\%ARITH"];




lin
	int i = const i.s;
	IntegerCConforms2RealC = ss ["Integer conforms to Real"];
	IntegerCConforms2IntegerC = ss ["Integer conforms to Integer"];

printname 
	int 			= ["arbitrary integer number"]
		++ ["\\$select from the list of previously entered integers or enter a new one"]
		++ ["\\%NUM{numerals}"];
	IntegerCConforms2RealC 	= ["Integer as a subtype of Real"];
	IntegerCConforms2IntegerC 	= ["Integer\\$Integer as a subtype of itself"];
--
-- Real
--
lin RealC = stdClass "Real";
	RealCConforms2RealC = ss ["Real conforms to Real"];
lin
--	realEq a b = infix eqP "=" a b;
--	realNeq a b = infix eqP "<>" a b;
	realAdd a b = infix addP "+" a b;
	realSub a b = infixL addP "-" a b;
	realUnaryMinus a = prefix unP "-" a;
	realTimes a b = infix multP "*" a b;
	realDiv a b = infixL multP "/" a b;
	realAbs a = dotOper0 a "abs";
	realFloor a = dotOper0 a "floor";
	realRound a = dotOper0 a "round";
	realMax a b = dotOper1 a "max" b;
	realMin a b = dotOper1 a "min" b;
	realLT a b = infix gtP "<" a b;
	realGT a b = infix gtP ">" a b;
	realLTE a b = infix gtP "<=" a b;
	realGTE a b = infix gtP ">=" a b;


    decremented exp decr = {
        s0 = (
            infix eqP "=" 
            exp
            (infix addP "-" 
                (mkAtPre exp)
                decr)
        ).s0;
        s1 = ["*** NOT ALLOWED ***"]; -- no atPre for this construction
        isAtpre = False;
        p = eqP
    };

    incremented exp decr = {
        s0 = (
            infix eqP "=" 
            exp
            (infix addP "+" 
                (mkAtPre exp)
                decr)
        ).s0;
        s1 = ["*** NOT ALLOWED ***"]; -- no atPre for this construction
        isAtpre = False;
        p = eqP
    };


printname
	RealC		= ["Real\\$<html>real number<br>In OCL these numbers are like those in mathematics, infinite and exact.</html>"]
		++ ["\\%PREDEF"];
	RealCConforms2RealC 	= ["Real\\$Real as a subtype of itself"];
	realAdd 	= ["+ for reals\\$<html>real<sub>1</sub> + real<sub>2</sub></html>"]
		++ ["\\%ARITH"]
		++ ["\\#!real1 The first argument"]
		++ ["\\#!real2 The second argument"];
	realSub 	= ["- for reals\\$<html>real<sub>1</sub> - real<sub>2</sub></html>"]
		++ ["\\%ARITH"]
		++ ["\\#!real1 The first argument"]
		++ ["\\#!real2 The second argument"];
	realUnaryMinus 	= ["unary minus for reals\\$<html>-real<sub>1</sub></html>"]
		++ ["\\%ARITH"]
		++ ["\\#!real The number, which is to be negated"];
	realTimes 	= ["* for reals\\$<html>real<sub>1</sub> * real<sub>2</sub></html>"]
		++ ["\\%ARITH"]
		++ ["\\#!real1 The first argument"]
		++ ["\\#!real2 The second argument"];
	realDiv 	= ["/ for reals\\$<html>real<sub>1</sub> / real<sub>2</sub></html>"]
		++ ["\\%ARITH"]
		++ ["\\#!real1 The first argument"]
		++ ["\\#!real2 The second argument"];
	realAbs 	= ["absolute value of an real\\$<html>|real<sub>1</sub>|</html>"]
		++ ["\\%ARITH"]
		++ ["\\#!real The number, from which the absolute value is wanted"];
	realFloor 	= ["floor\\$The largest integer which is less than or equal to the given real"]
		++ ["\\%ARITH"]
		++ ["\\#real The number, that is to be floored"];
	realRound	= ["rounding\\$The integer that is closest to the given real. If there are two such integers, the larger one."]
		++ ["\\%ARITH"]
		++ ["\\#real The number, that is to be rounded"];
	realMax 	= ["maximum of two reals\\$<html><i>max</i>(real<sub>1</sub>, real<sub>2</sub>)<br>in OCL: real<sub>1</sub>.max(real<sub>2</sub>)</html>"]
		++ ["\\%ARITH"]
		++ ["\\#!real1 The first argument"]
		++ ["\\#!real2 The second argument"];
	realMin 	= ["minimum of two reals\\$<html><i>min</i>(real<sub>1</sub>, real<sub>2</sub>)<br>in OCL: real<sub>1</sub>.min(real<sub>2</sub>)</html>"]
		++ ["\\%ARITH"]
		++ ["\\#!real1 The first argument"]
		++ ["\\#!real2 The second argument"];
	realLT		= ["less than\\$<html><i>less then</i> comparison of two reals (or integers, if casted)<br>real<sub>1</sub> &lt; real<sub>2</sub></html>"]
		++ ["\\%COMP"]
		++ ["\\#!real1 The first argument"]
		++ ["\\#!real2 The second argument"];
	realGT		= ["greater than\\$<html><i>greater then</i> comparison of two reals (or integers, if casted)<br>real<sub>1</sub> &gt; real<sub>2</sub></html>"]
		++ ["\\%COMP"]
		++ ["\\#!real1 The first argument"]
		++ ["\\#!real2 The second argument"];
	realLTE		= ["less than or equal\\$<html><i>less then or equal to</i> comparison of two reals (or integers, if casted)<br>real<sub>1</sub> &lt;= real<sub>2</sub></html>"]
		++ ["\\%COMP"]
		++ ["\\#!real1 The first argument"]
		++ ["\\#!real2 The second argument"];
	realGTE		= ["greater than or equal\\$<html><i>greater then or equal</i> comparison of two reals (or integers, if casted)<br>real<sub>1</sub> &gt;= real<sub>2</sub></html>"]
		++ ["\\%COMP"]
		++ ["\\#!real1 The first argument"]
		++ ["\\#!real2 The second argument"];


--
-- Bool
--
lin 
	BooleanC = stdClass "Boolean";
	BooleanCConforms2BooleanC = ss ["Boolean conforms to Boolean"];
	true = const "true";
	false = const "false";
	notBool a = prefix unP "not" a;
--	boolEq a b = infix eqP "=" a b;
	orBool a b = infix andP "or" a b;
	andBool a b = infix andP "and" a b;
	xorBool a b = infix andP "xor" a b;
	impliesBool a b = infixR impP "implies" a b;

printname
	BooleanC	= ["Boolean"]
		++ ["\\$The OCL type Boolean represents the common true/false values."]
		++ ["\\%PREDEF"];
	BooleanCConforms2BooleanC = ["Boolean\\$Boolean as a subtype of itself"];
	true 		= ["true"]
		++ ["\\$The truth value for true"]
		++ ["\\%BOOL{boolean operators}"];
	false 		= ["false"]
		++ ["\\$The truth value for false"]
		++ ["\\%BOOL"];
	notBool		= ["boolean not"]
		++ ["\\$true iff the given boolean is false"]
		++ ["\\%BOOL"]
		++ ["\\#bool The Boolean that is to be negated"];
	orBool		= ["boolean or"]
		++ ["\\$true iff at least one of <i>a</i> and <i>b</i> is true"]
		++ ["\\%BOOL"]
		++ ["\\#a the first Boolean"]
		++ ["\\#b the second Boolean"];
	andBool		= ["boolean and\\$true iff both <i>a</i> and <i>b</i> are true"]
		++ ["\\%BOOL"]
		++ ["\\#a the first Boolean"]
		++ ["\\#b the second Boolean"];
	xorBool		= ["boolean exclusive or"]
		++ ["\\$true iff exactly one of the given booleans is true"]
		++ ["\\%BOOL"]
		++ ["\\#a the first Boolean"]
		++ ["\\#b the second Boolean"];
	impliesBool	= ["boolean implication"]
		++ ["\\$true iff the first given boolean is false or both are true"]
		++ ["\\%BOOL"]
		++ ["\\#a the first Boolean"]
		++ ["\\#b the second Boolean"];

	

--
-- Sent
--
lin sentEq a b = infix eqP "=" a b;
	notS a = prefix unP "not" a;	
	orS a b = infix andP "or" a b;
	andS a b = infix andP "and" a b;
	xorS a b = infix andP "xor" a b;
	impliesS a b = infixR impP "implies" a b; 
	
	oneAnd s1 s2 = infix andP "and" s1 s2;
	consAnd t a = infix andP "and" t a;
	posAndList2Sent a = a;
	negAndList2Sent a = prefix unP "not" a;
	
	oneOr s1 s2 = infix andP "or" s1 s2;
	consOr t a = infix andP "or" t a;
	posOrList2Sent a = a;
	negOrList2Sent a = prefix unP "not" a;

printname
	sentEq		= ["equivalence of sentences"]
		++ ["\\$true iff both propositions evaluate to the same truth value"]
		++ ["\\%BOOL{boolean operators for sentences}"]
		++ ["\\#sentence1 the first of the two equivalent sentences"]
		++ ["\\#sentence2 the second of the two equivalent sentences"];
	notS		= ["boolean 'not' for a sentence"]
		++ ["\\$true iff the given sentence is equivalent to false"]
		++ ["\\%BOOL"]
		++ ["\\#sentence The proposition that is to be negated"];
	orS		= ["boolean 'or' for sentences"]
		++ ["\\$true iff at least one of sentence1 and sentence2 is equivalent to true"]
		++ ["\\%BOOL"]
		++ ["\\#sentence1 the first of the two propositions"]
		++ ["\\#sentence2 the second of the two propositions"];
	andS		= ["boolean 'and' for sentences"]
		++ ["\\$true iff both sentence1 and sentence2 are equivalent to true"]
		++ ["\\%BOOL"]
		++ ["\\#sentence1 the first of the two propositions"]
		++ ["\\#sentence2 the second of the two propositions"];
	xorS		= ["boolean 'exclusive or' for sentences"]
		++ ["\\$true iff either sentence1 or sentence2, but not both, are equivalent to true"]
		++ ["\\%BOOL"]
		++ ["\\#sentence1 the first of the two sentences"]
		++ ["\\#sentence2 the second of the two sentences"];
	impliesS	= ["boolean 'implication' for sentences"]
		++ ["\\$this is true, iff:<br><i>condition</i> is false<br>or <i>condition</i> is true and <i>conclusion</i> also is true"]
		++ ["\\%BOOL"]
		++ ["\\#condition the condition of when <i>conclusion</i> must be true"]
		++ ["\\#conclusion the sentence that must hold if <i>condition</i> is true"];

	oneAnd		= ["2 and-conjoined sentences as a list\\$to finish a list of and-conjoined sentences"];
	consAnd		= ["list of and-conjoined sentences\\$<html>for a bulleted list of and-conjoined sentences<br>Example:<br> all of the following conditions are true: <br><ul> <li> something is true </i> <li> another thing is also true </i><li> something else is not true </i></ul> </html>"];
	posAndList2Sent	= ["use an and-conjoined list as a single sentence\\%LIST{build lists}"];
	negAndList2Sent	= ["negate an and-conjoined list and use it as a single sentence\\%LIST"];

	oneOr		= ["2 or-conjoined sentences as a list\\$to finish a list of or-conjoined sentences"];
	consOr		= ["list of or-conjoined sentences\\$<html>for a bulleted list of or-conjoined sentences<br>Example:<br> at least one of the following conditions is true: <br><ul> <li> something is true </i> <li> another thing is also true </i><li> something else is not true </i></ul> </html>"];
	posOrList2Sent	= ["use an or-conjoined list as a single sentence\\%LIST"];
	negOrList2Sent 	= ["negate an or-conjoined list and use it as a single sentence\\%LIST"];

	
	
lin 
	ifThenElse _ cond t e = {
		s0 = "if" ++ noParen cond ++ "then" ++ noParen t ++ "else" ++ noParen e ++ "endif"; 
		s1 = "if" ++ noParen cond ++ "then" ++ noParen t ++ "else" ++ noParen e ++ ["endif @pre"]; -- erroneous 
		p = ifP;
		isAtpre = False
	};
	
	ifThenElseS cond t e = {
		s0 = "if" ++ noParen cond ++ "then" ++ noParen t ++ "else" ++ noParen e ++ "endif"; 
		s1 = "if" ++ noParen cond ++ "then" ++ noParen t ++ "else" ++ noParen e ++ ["endif @pre"]; -- erroneous 
		p = ifP;
		isAtpre = False
	};

printname
	ifThenElse	= ["if-then-else selection"]
		++ ["\\$if <i>a</i> then <i>b</i>, otherwise <i>c</i>"]
		++ ["\\%BOOL"]
		++ ["\\#class The class of the then- and the else-value"]
		++ ["\\#condition The boolean that selects between then and else"]
		++ ["\\#then-case This value of type <i>class</i> is taken if <i>condition</i> is true"]
		++ ["\\#else-case This value of type <i>class</i> is taken if <i>condition</i> is false"];
	ifThenElseS	= ["if-then-else for sentences"]
		++ ["\\$if <i>condition</i> then <i>then-proposition</i>, otherwise <i>else=propsition</i>"]
		++ ["\\%BOOL"]
		++ ["\\#condition the boolean that selects between then and else"]
		++ ["\\#then-proposition this proposition has to hold if <i>condition</i> is true"]
		++ ["\\#else-proposition this proposition has to hold if <i>condition</i> is false"];
	
-- 
-- String
--
lin StringC = stdClass "String";
	StringCConforms2StringC = ss ["String conforms to String"];
--	stringEq a b = infix eqP "=" a b;
	stringLiteral lit = const (lit.s);
	stringSize s = dotOper0 s "size";
	stringConcat a b = dotOper1 a "concat" b;
	stringToUpper s = dotOper0 s "toUpper";
	stringToLower s = dotOper0 s "toLower";
	stringSubstring s a b = dotOper s "substring" (noParen a ++ "," ++ noParen b);

printname
	StringC		= ["String"]
		++ ["\\$The OCL type String represents Strings of ASCII characters or multi-byte characters."]
		++ ["\\%PREDEF"];
	StringCConforms2StringC = ["String\\$String as a subtype of itself"];
	stringLiteral 	= ["arbitrary String"]
		++ ["\\$select from the list of previously entered strings or enter a new one"];
	stringSize 	= ["string size"]
		++ ["\\$The number of characters in <i>string</i>"]
		++ ["\\%STRING{String operations}"]
		++ ["\\#string The String whose characters are to be counted"];
	stringConcat 	= ["concatenate two strings"]
		++ ["\\$Concatenating 'abs' and 'esp' results in 'absesp'."]
		++ ["\\%STRING"]
		++ ["\\#string1 The first String"]
		++ ["\\#string2 The second String"];
	stringToUpper 	= ["convert to uppercase"]
		++ ["\\$Convert all characters in <i>string</i> to uppercase"]
		++ ["\\%STRING"]
		++ ["\\#string The String that is wanted in uppercase characters"];
	stringToLower 	= ["convert to lowercase"]
		++ ["\\$Convert all characters in <i>string</i> to lowercase"]
		++ ["\\%STRING"]
		++ ["\\#string The String that is wanted in lowercase characters"];
	stringSubstring	= ["substring of string"]
		++ ["\\$<pre>'1234567'.substring(2,5)</pre> is <pre>'2345'.</pre>"]
		++ ["\\%STRING"]
		++ ["\\#string The original String"]
		++ ["\\#start The position of the first character in the substring"]
		++ ["\\#end The position of the last character in the substring<br>This character is included (unlike in Java for example)."];

--
-- Iterators (N.B.: not used for the OCL "iterate" construction!)
--

lin	instIterSingle varC _ body = {s1 = body.v; s2 = ":" ++ varC.s; 
		s3 = inst2str {s0=body.s0; s1=body.s1; p=body.p; isAtpre=body.isAtpre}};
	instIterMany varC _ body = { s1 = body.v ++ "," ++ body.s1; s2 = ":" ++ varC.s;
		s3 = body.s3};

lin sentIterSingle varC body = {s1 = body.v; s2 = ":" ++ varC.s; 
		s3 = inst2str {s0=body.s0; s1=body.s1; p=body.p; isAtpre=body.isAtpre}};
	sentIterMany varC body = { s1 = body.v ++ "," ++ body.s1; s2 = ":" ++ varC.s;
		s3 = body.s3};
printname
	instIterSingle = ["say sth. about one element at a time"]
		++ ["\\$introduces a new variable of given type <i>type</i> that can be accessed in <i>body</i>."]
		++ ["\\%ITER{iterators}"]
		++ ["\\#elemType The type of the elements of <i>collection</i>"]
		++ ["\\#resultType The type the unique expression in <i>body</i> has"]
		++ ["\\#collection A Collection with parameter type <i>elemType</i>"]
		++ ["\\#body A boolean expression that can refer to a new variable of type <i>class</i> that represents the current element."];	
	instIterMany = ["say sth. about several elements at a time"]
		++ ["\\$introduces a new variable of given type <i>type</i> that can be accessed in <i>body</i>."]
		++ ["\\%ITER"]
		++ ["\\#elemType The type of the elements of <i>collection</i>"]
		++ ["\\#resultType The type the unique expression in <i>body</i> has"]
		++ ["\\#iterator Further introduced variables that can be accessed in the <i>body</i> of the last added iterator."];	
        sentIterSingle = ["say sth. about one element at a time"]
                ++ ["\\$introduces a new variable of given type <i>type</i> that can be accessed in <i>body</i>."]
                ++ ["\\%ITER"]
                ++ ["\\#elemType The type of the elements"]
		++ ["\\#collection A Collection with parameter type <i>elemType</i>"]
                ++ ["\\#body A boolean expression that can refer to a new variable of type <i>class</i> that represents the current element."];   
	sentIterMany = ["say sth. about several elements at a time"]
		++ ["\\$introduces a more a variable of given type <i>type</i> that can be accessed in <i>body</i> and enables the introduction of further variables."]
		++ ["\\%ITER"]
		++ ["\\#class The type of the elements"]
		++ ["\\#iterator furter introduced variables that can be accessed in the <i>body</i> of the last added iterator."];	



--
-- collections
--
lin
	Collection c = stdClass ("Collection" ++ c.s);
	size _ coll = arrowOper0 coll "size";
	includes _ _ coll a = arrowOper1 coll "includes" a; 
	excludes _ _ coll a = arrowOper1 coll "excludes" a;
	count _ coll a = arrowOper1 coll "count" a;
	includesAll _ coll1 coll2 = arrowOper1 coll1 "includesAll" coll2;
	excludesAll _ coll1 coll2 = arrowOper1 coll1 "excludesAll" coll2;
	isEmpty _ coll = arrowOper coll "isEmpty" "";
	notEmpty _ coll = arrowOper coll "notEmpty" "";
	sum _ coll = arrowOper coll "sum" "";
	exists c coll i = arrowOper coll "exists" (wrapIter i);
		-- arrow1 coll (app1 "exists" (wrapIter i));
	forAll c coll i = arrowOper coll "forAll" (wrapIter i);
	isUnique c d coll i = arrowOper coll "isUnique" (wrapIter i);
	sortedBy c d coll i = arrowOper coll "sortedBy" (wrapIter i);
	iterate c a coll init body = arrowOper coll "iterate" ( 
		body.v0 ++ ":" ++ c.s ++ ";" ++    -- this is the "element", same type as the collection
		body.v1 ++ ":" ++ a.s ++ "=" ++    -- this is the "accumulator", same type as the result
		(noParen init) ++ "|" ++
		(noParen {s0=body.s0; s1=body.s1; p=body.p; isAtpre = False})  -- NB: "noParen body"  does not work with GF!?
		);
	any c coll i = arrowOper coll "any" (wrapIter i);
	one c coll i = arrowOper coll "one" (wrapIter i);
	collConforms sub super p = ss (["Collection ("] ++ sub.s ++ [") conforms to Collection ("] ++ super.s ++ ["), since"] ++ p.s);
	
printname
	Collection 	= ["Collection(paramType)"]
		++ ["\\$<html><i>Collection</i> is the abstract supertype of all other collection types in OCL. <br>Collections always have a parameter type, the type of their elements.</html>"] 
		++ ["\\%PREDEF"]
		++ ["\\#elemType the type of the elements of this Collection.<br>Collection with differently typed elements have themselves different types."];

	size		= ["size of collection"] 
		++ ["\\$The number of elements in the given collection."] 
		++ ["\\%COLL{collection operations\\$Operations on collections predefined in OCL.<br>These operate on the OCL collection types, not on Vectors, AbstractLists of the implementation language.}"] 
		++ ["\\#elemType The type of the elements of <i>coll</i>"] 
		++ ["\\#coll The Collection whose elements are to be counted.<br>This Collection must be parametrized with (elemType)"];

	includes	= ["element is included in collection"] 
		++ ["\\$True iff the given object is an element of the given collection."] 
		++ ["\\%COLL"] 
		++ ["\\#collElemType The official element type of <i>coll</i>.<br>That is, the parameter type of <i>coll</i>"] 
		++ ["\\#instType The type of <i>elem</i>."] 
		++ ["\\#elem The instance that has to be an element of <i>coll</i>."]
		++ ["\\#coll The Collection which must include an element.<br>This Collection must be parametrized with (collElemType)"];

	excludes	= ["element is not included in collection"] 
		++ ["\\$False iff the given object is an element of the given collection."] 
		++ ["\\%COLL"] 
		++ ["\\#collElemType The official element type of <i>coll</i>.<br>That is, the parameter type of <i>coll</i>"] 
		++ ["\\#instType The type of <i>elem</i>."] 
		++ ["\\#elem The instance that must not be an element of <i>coll</i>."]
		++ ["\\#coll The Collection which must not include an element.<br>This Collection must be parametrized with (collElemType)"];

	count		= ["count the occurances of an object in the collection."] 
		++ ["\\%COLL"] 
		++ ["\\#collElemType The official element type of <i>coll</i>.<br>That is, the parameter type of <i>coll</i>"] 
		++ ["\\#coll The Collection in which occurances of <i>elem</i> are to be counted."] 
		++ ["\\#!elem The instance of which the occurances in <i>coll</i> are counted."];

	includesAll	= ["one collection is 'subset' of another"] 
		++ ["\\$Does the first collection contain all elements of the second?"] 
		++ ["\\%COLL"] 
		++ ["\\#elemType The parameter type (element type) of both collections"] 
		++ ["\\#!superset The Collection with element type <i>elemType</i> that should contain all elements of <i>subset</i>."] 
		++ ["\\#!subset The Collection whose elements should all be in <i>superset</i> too."];

	excludesAll	= ["elements of one collection are not in another"] 
		++ ["\\$Does collection1 contain no elements of collection2?"] 
		++ ["\\%COLL"] 
		++ ["\\#elemType The parameter type (element type) of both collections"]
		++ ["\\#!collection1 The collection that should not contain elements from <i>collection2</i>"] 
		++ ["\\#!collection2 The Collection whose elements should not be in <i>collection1</i>."];

	isEmpty		= ["is empty collection"] 
		++ ["\\$Is the given collection the empty collection?"] 
		++ ["\\%COLL"] 
		++ ["\\#elemType The parameter type (element type) of <i>coll</i>."] 
		++ ["\\#coll The collection with element type <i>elemType</i> that should be the empty Collection."];

	notEmpty	= ["is non-empty collection"] 
		++ ["\\$Is the given collection not the empty collection?"] 
		++ ["\\%COLL"] 
		++ ["\\#elemType The parameter type (element type) of <i>coll</i>."] 
		++ ["\\#coll The collection with element type <i>elemType</i> that should not be empty."];

	sum		= ["sum over elements"] 
		++ ["\\$The result of the addition of all elements in the given collection. <br>Elements must support '+'. Integer and Real do."] 
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type (element type) of <i>coll</i>."] 
		++ ["\\#coll The collection with element type <i>elemType</i> over whose elements the sum should be calculated."];

	exists		= ["element fulfills condition"] 
		++ ["\\$True iff the given expression evaluates to true for at least one element in the given collection."] 
		++ ["\\%COLL"] 
		++ ["\\#elemType The parameter type (element type) of <i>coll</i>."] 
		++ ["\\#coll The collection with element type <i>elemType</i> whose elements should fulfill the given condition"] 
		++ ["\\#iterator The boolean condition that should be fulfilled by at least one element."];

	forAll		= ["all elements fulfill condition"] 
		++ ["\\$True iff the given expression evaluates to true for all elements of the collection."] 
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type (element type) of <i>coll</i>."] 
		++ ["\\#coll The collection with element type <i>elemType</i> that should contain the element"] 
		++ ["\\#iterator Introduce a name to address each element one at a time and a boolean condition that each element has to fulfill.<br>If two names are listed here, this is the same as operating on the cartesian product of <i>coll</i> with itself."];

	isUnique	= ["expression is unique for all elements"]
		++ ["\\$True iff the given expression evaluates to a different value for each element in the given collection."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>collection</i>"]
		++ ["\\#resultType The type of the unique expression in <i>body</i>"]
		++ ["\\#collection The collection with the unique element, has parameter type <i>elemType</i>"]
		++ ["\\#body The expression together with a bound variable to access each single element"];

	sortedBy	= ["sort collection"]
		++ ["\\$Sorts with &lt; so least comes first and results in a Sequence. The &lt; operator must be defined for the element type."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>collection</i>"]
		++ ["\\#sortType The type of <i>body</i>"]
		++ ["\\#collection The collection that should be sorted"]
		++ ["\\#body An expression of type <i>sortType</i> together with a bound variable to access each individual element"];

	iterate		= ["iterate over collection"]
		++ ["\\$Calculate an expression iteratively over all elements of a collection. <br>For that, the accumulator is initialized with <i>init</i> and then for each element in <i>collection</i> the expression in <i>body</i> is evaluated and assigned to the accumulator."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>collection</i>"]
		++ ["\\#resultType The type of the resulting expression in <i>body</i>"]
		++ ["\\#collection The collection that is the basis for the calculation.<br>The parameter type is <i>elemType</i>."]
		++ ["\\#init The initial value of the collecting bound variable, of type <i>resultType</i>"]
		++ ["\\#body An expression of type <i>resultType</i> that contains an accumulator and <i>collection</i> as bound variables."];

	any		= ["pick suiting element"]
		++ ["\\$Returns one arbitrary element of the collection, which fulfills the condition given in <i>body</i>. <br>If no such element exists, <i>undefined</i> is returned."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>collection</i>"]
		++ ["\\#collection The collection from which an element should be chosen.<br>The parameter type is <i>elemType</i>."]
		++ ["\\#body The condition together with a bound variable to access each single element"];

	one		= ["exactly one element fulfills condition"]
		++ ["\\$True iff exactly one element in the collection fulfills the condition given in <i>body</i>."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>collection</i>"]
		++ ["\\#collection The collection which should contain only one such element.<br>The parameter type is <i>elemType</i>."]
		++ ["\\#body The condition together with a bound variable to access each single element"];


	collConforms	= ["collection type is subtype of Collection"];

--
-- Set
--
lin	Set c = stdClass ("Set" ++ c.s);
	unionSS c set1 set2 = arrowOper1 set1  "union" set2;
	unionSB c set bag = arrowOper1 set "union" bag;
	intersectionSS c set1 set2 = arrowOper1 set1 "intersection" set2;
	intersectionSB c set bag = arrowOper1 set "intersection" bag;
	subS c set1 set2 = infixL addP "-" set1 set2;
	includingS c set a = arrowOper1 set "including" a;
	excludingS c set a = arrowOper1 set "excluding" a;
	symmetricDiff c set1 set2 = arrowOper1 set1 "symmetricDifference" set2;
	selectSet c set i = arrowOper set "select" (wrapIter i);
	rejectSet c set i = arrowOper set "reject" (wrapIter i);
	collectSet c d set i = arrowOper set "exists" (wrapIter i); 
	countSet c set a = arrowOper1 set "count" a;
	setAsSequence c set = arrowOper set "asSequence" "";
	setAsBag c set = arrowOper set "asBag" "";
	setConforms sub super p = ss (["Set ("] ++ sub.s ++ [") conforms to Set ("] ++ super.s ++ ["), since"] ++ p.s);
	setConforms2coll sub super elemC = ss (["Set ("] ++ sub.s ++ [") conforms to Collection ("] ++ super.s ++ ")");

printname
	Set		= ["Set(paramType)"] 
		++ ["\\$Mathematical set that does not contain duplicates. <br>Sets always have a parameter type, the type of their elements."] 
		++ ["\\%PREDEF"];

	unionSS		= ["union of two Sets"] 
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of both Sets"] 
		++ ["\\#set1 the first Set, has to have the parameter type <i>elemType</i>"] 
		++ ["\\#set2 the second Set, has to have the parameter type <i>elemType</i>"];

	unionSB		= ["union of a Set and a Bag"] 
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of both <i>set</i> and <i>bag</i>"] 
		++ ["\\#set The Set, has to have the parameter type <i>elemType</i>"] 
		++ ["\\#bag The Bag, has to have the parameter type <i>elemType</i>"];

	intersectionSS	= ["intersection of two Sets"] 
		++ ["\\$Returns a set that contains all elements, that are in both sets."] 
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of both Sets"]
		++ ["\\#set1 the first Set, has to have the parameter type <i>elemType</i>"]
		++ ["\\#set2 the second Set, has to have the parameter type <i>elemType</i>"];

	intersectionSB	= ["intersection of a Set and a Bag"] 
		++ ["\\$Returns a set that contains all elements, that are in both <i>set</i> and <i>bag</i>."] 
		++ ["\\%COLL"] 
		++ ["\\#elemType The parameter type of both <i>set</i> and <i>bag</i>"] 
		++ ["\\#set The Set, has to have the parameter type <i>elemType</i>"] 
		++ ["\\#bag The Bag, has to have the parameter type <i>elemType</i>"];

	subS		= ["set subtraction"] 
		++ ["\\$The elements of <i>originalSet</i>, which are not in <i>takeAway</i>."] 
		++ ["\\%COLL"] 
		++ ["\\#elemType The parameter type of both Sets"] 
		++ ["\\#originalSet The Set from which the elements of <i>takeAway</i> get removed.<br>Has to have the parameter type <i>elemType</i>"] 
		++ ["\\#takeAway The Set whose elements are removed from <i>originalSet</i>.<br>Has to have the parameter type <i>elemType</i>."];

	includingS	= ["put object in set"] 
		++ ["\\$The Set with the elements of the Set plus the object."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>set</i>"]
		++ ["\\#set The Set which should gain <i>object</i>"]
		++ ["\\#object The object of type <i>elemType</i> that is to be added to <i>set</i>."];

	excludingS	= ["put object out of set"] 
		++ ["\\$The Set with the elements of the Set but not the object."] 
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>set</i>"]
		++ ["\\#set The Set which should lose <i>object</i>"]
		++ ["\\#object The object of type <i>elemType</i> that is to be removed from <i>set</i>."];

	symmetricDiff	= ["symmetric difference of Sets"]
		++ ["\\$The Set containing all the elements that are in only one of the Sets."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of both Sets"]
		++ ["\\#set1 the first Set, has to have the parameter type <i>elemType</i>"]
		++ ["\\#set2 the second Set, has to have the parameter type <i>elemType</i>"];

	selectSet	= ["select from Set"]
		++ ["\\$The subset of the Set for which the given expression is true."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>set</i>"]
		++ ["\\#set The Set from which some elements should be selected"]
		++ ["\\#body The boolean expression that is the selection predicate, together with the introduction of a bound variable to access each element one at a time"];

	rejectSet	= ["select from Set"]
		++ ["\\$The subset of the Set for which the given expression is false."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>set</i>"]
		++ ["\\#set The Set from which some elements should be selected"]
		++ ["\\#body The boolean expression that is the selection predicate, together with the introduction of a bound variable to access each element one at a time"];

	collectSet	= ["collect results of an expression over a Set"]
		++ ["\\$The Bag of elements that result from applying the given expression to every member of the Set.<br>Used, when something should be done with all elements of a Set."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>set</i>"]
		++ ["\\#resultType The type of the result, specified in the expression <i>body</i>."]
		++ ["\\#set The Set from which the wanted values should be calculated."]
		++ ["\\#body Here it is stated what should be done with each element of <i>set</i>.<br>This can be a calculation, an attribute access or an arbitrary expression of type <i>resultType</i> together with a bound variable to access each individual element"];

	countSet	= ["count the occurances of an object in the Set"] 
		++ ["\\$The number of occurrences of the given object in the Set."] 
		++ ["\\%COLL"] 
		++ ["\\#setElemType The official element type of <i>set</i>.<br>That is, the parameter type of <i>set</i>."] 
		++ ["\\#set The Set in which occurances of <i>elem</i> are to be counted."] 
		++ ["\\#elem The instance of which the occurances in <i>set</i> are counted."];

	setAsSequence	= ["set as sequence"] 
		++ ["\\$Returns a Sequence that contains all all the elements of the Set in undefined order."]
		++ ["\\%COLL"]
		++ ["\\#setElemType The official element type of <i>set</i>.<br>That is, the parameter type of <i>set</i>"]
		++ ["\\#set The Set with parameter type <i>setElemType</i>."];

	setAsBag	= ["set as bag"]
		++ ["\\$Returns a Bag that contains all all the elements of the Set."]
		++ ["\\%COLL"]
		++ ["\\#setElemType The official element type of <i>set</i>.<br>That is, the parameter type of <i>set</i>"]
		++ ["\\#set The Set with parameter type <i>setElemType</i>."];

	setConforms2coll= ["upcast Set to Collection"]
		++ ["\\$Set as a subtype of Collection."]
		++ ["\\#subtype The parameter type that is a subtype of <i>supertype</i>"]
		++ ["\\#supertype The parameter type that is a supertype of <i>subtype</i>"]
		++ ["\\#inheritance A special proof object, or so-called witness, that is only available for types, for which <i>subtype</i> really is a subtype of <i>supertype</i>."];

	setConforms	= ["upcast parameter type of Set"] 
		++ ["\\$In OCL a (Set <i>subtype</i>) is subtype of (Set <i>supertype</i>)"]
		++ ["\\#subtype The parameter type that is a subtype of <i>supertype</i>"]
		++ ["\\#supertype The parameter type that is a supertype of <i>subtype</i>"]
		++ ["\\#inheritance A special proof object, or so-called witness, that is only available for types, for which <i>subtype</i> really is a subtype of <i>supertype</i>."];



--
-- Bag
--
lin	Bag c = stdClass ("Bag" ++ c.s);
	unionBB _ a b = arrowOper1 a "union" b;
	unionBS _ a b = arrowOper1 a "union" b;
	intersectionBB _ a b = arrowOper1 a "intersection" b;
	intersectionBS _ a b = arrowOper1 a "intersection" b;
	includingB _ bag e = arrowOper1 bag "including" e;
	excludingB _ bag e = arrowOper1 bag "excluding" e;
	selectBag _ bag i = arrowOper bag "select" (wrapIter i);
	rejectBag _ bag i = arrowOper bag "reject" (wrapIter i);
	collectBag _ _  bag i = arrowOper bag "collect" (wrapIter i);
	countBag _ bag e = arrowOper1 bag "count" e;
	bagAsSequence _ bag = arrowOper0 bag "asSequence";
	bagAsSet _ bag = arrowOper0 bag "asSet";
	bagConforms sub super p = ss (["Bag ("] ++ sub.s ++ [") conforms to Bag ("] ++ super.s ++ ["), since"] ++ p.s);	
	bagConforms2coll sub super elemC = ss (["Bag ("] ++ sub.s ++ [") conforms to Collection ("] ++ super.s ++ ")");

printname	
	Bag		= ["Bag(paramType)"]
		++ ["\\$Unordered collection of objects in which an object can occur multiple times. <br>Bags always have a parameter type, the type of their elements."]
		++ ["\\%PREDEF"];
	unionBB		= ["union of two Bags"]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of both Bags"] 
		++ ["\\#bag1 the first Bag, has to have the parameter type <i>elemType</i>"] 
		++ ["\\#bag2 the second Bag, has to have the parameter type <i>elemType</i>"];

	unionBS		= ["union of a Bag and a Set\\%COLL"]
		++ ["\\#elemType The parameter type of both <i>bag</i> and <i>set</i>"] 
		++ ["\\#bag The Bag, has to have the parameter type <i>elemType</i>"]
		++ ["\\#set The Set, has to have the parameter type <i>elemType</i>"]; 

	intersectionBB	= ["intersection of two Bags"]
		++ ["\\$Returns a Bag that contains all elements, that are in both Bags."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of both Bags"]
		++ ["\\#bag1 The first Bag, has to have the parameter type <i>elemType</i>"]
		++ ["\\#bag2 The second Bag, has to have the parameter type <i>elemType</i>"];
	intersectionBS	= ["intersection of a Bag and a Set"]
		++ ["\\$Returns a bag that contains all elements, that are in both the Bag and the Set."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of both <i>bag</i> and <i>set</i>"] 
		++ ["\\#bag The Bag, has to have the parameter type <i>elemType</i>"]
		++ ["\\#set The Set, has to have the parameter type <i>elemType</i>"];
	includingB	= ["put object in bag"]
		++ ["\\$The Bag with the elements of the Bag plus the object."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>bag</i>"]
		++ ["\\#bag The Bag which should gain <i>object</i>"]
		++ ["\\#object The object of type <i>elemType</i> that is to be added to <i>bag</i>."];
	excludingB	= ["put object out of bag"]
		++ ["\\$The Bag with the elements of the Bag but without all occurrences of the object."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>bag</i>"]
		++ ["\\#bag The Bag which should lose <i>object</i>"]
		++ ["\\#object The object of type <i>elemType</i> that is to be removed from <i>bag</i>."];
	selectBag	= ["select from bag"]
		++ ["\\$The subset of the Bag for which the given expression is true."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>bag</i>"]
		++ ["\\#set The Bag from which some elements should be selected"]
		++ ["\\#body The boolean expression that is the selection predicate, together with the introduction of a bound variable to access each element one at a time"];
	rejectBag	= ["reject from bag"]
		++ ["\\$The subset of the Bag for which the given expression is false."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>bag</i>"]
		++ ["\\#bag The Bag from which some elements should be selected"]
		++ ["\\#body The boolean expression that is the selection predicate, together with the introduction of a bound variable to access each element one at a time"];
	collectBag	= ["collect results of an expression over a Bag"]
		++ ["\\$The Bag of elements that result from applying the given expression to every member of the Bag."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>bag</i>"]
		++ ["\\#resultType The type of the result, specified in the expression <i>body</i>."]
		++ ["\\#bag The Set from which the wanted values should be calculated."]
		++ ["\\#body Here it is stated what should be done with each element of <i>bag</i>.<br>This can be a calculation, an attribute access or an arbitrary expression of type <i>resultType</i> together with a bound variable to access each individual element"];
	countBag	= ["count the occurances of an object in the Bag"]
		++ ["\\$The number of occurrences of the given object in the Bag."]
		++ ["\\%COLL"]
		++ ["\\#setElemType The official element type of <i>bag</i>.<br>That is, the parameter type of <i>bag</i>."]
		++ ["\\#bag The Bag in which occurances of <i>elem</i> are to be counted."]
		++ ["\\#elem The instance of which the occurances in <i>bag</i> are counted."];
	bagAsSequence	= ["bag as sequence"]
		++ ["\\$Returns a Sequence that contains all all the elements of the bag in undefined order."]
		++ ["\\%COLL"]
		++ ["\\#bagElemType The official element type of <i>bag</i>.<br>That is, the parameter type of <i>bag</i>"]
		++ ["\\#bag The Bag with parameter type <i>setElemType</i>."];
	bagAsSet	= ["bag as Set"]
		++ ["\\$Returns a Set that contains all all the elements of the Bag, with duplicates removed."] 
		++ ["\\%COLL"]
		++ ["\\#bagElemType The official element type of <i>bag</i>.<br>That is, the parameter type of <i>bag</i>"] 
		++ ["\\#bag The Bag with parameter type <i>bagElemType</i>."];
	bagConforms	= ["a collection type conforms to Bag"]
		++ ["\\$Cast another collection to Bag"]
		++ ["\\#subtype The parameter type that is a subtype of <i>supertype</i>"]
		++ ["\\#supertype The parameter type that is a supertype of <i>subtype</i>"]
		++ ["\\#inheritance A special proof object, or so-called witness, that is only available for types, for which <i>subtype</i> really is a subtype of <i>supertype</i>."];
	bagConforms2coll= ["upcast Bag to Collection"]
		++ ["\\$Bag as a subtype of Collection."]
		++ ["\\#subtype The parameter type that is a subtype of <i>supertype</i>"]
		++ ["\\#supertype The parameter type that is a supertype of <i>subtype</i>"]
		++ ["\\#inheritance A special proof object, or so-called witness, that is only available for types, for which <i>subtype</i> really is a subtype of <i>supertype</i>."];

		


--
-- Sequence
--
lin	Sequence c = stdClass ("Sequence" ++ c.s);
	unionSeq _ a b = arrowOper1 a "union" b;
	append _ a b = arrowOper1 a "append" b;
	prepend _ a b = arrowOper1 a "prepend" b;
	subSequence _ a start end = arrowOper a "subSequence" (noParen start ++ "," ++ noParen end);
	at _ a i = arrowOper1 a "at" i;
	first _ a = arrowOper0 a "first";
	last _ a = arrowOper0 a "last";
	includingSeq _ seq e = arrowOper1 seq "including" e;
	excludingSeq _ seq e = arrowOper1 seq "excluding" e;
	selectSeq _ seq i = arrowOper seq "select" (wrapIter i);
	rejectSeq _ seq i = arrowOper seq "reject" (wrapIter i);
	collectSeq _ _  seq i = arrowOper seq "collect" (wrapIter i);
	seqAsBag _ a = arrowOper0 a "asBag";
	seqAsSet _ a = arrowOper0 a "asSet";
	seqConforms sub super p = ss (["Sequence ("] ++ sub.s ++ [") conforms to Sequence ("] ++ super.s ++ ["), since"] ++ p.s);
	seqConforms2coll sub super elemC = ss (["Sequence ("] ++ sub.s ++ [") conforms to Collection ("] ++ super.s ++ ")");

printname	
	Sequence	= ["Sequence(paramType)"]
		++ ["\\$Ordered collection of objects in which an object can occur multiple times. <br>Sequences always have a parameter type, the type of their elements."]
		++ ["\\%PREDEF"];
	unionSeq	= ["concatenation of two Sequences"]
		++ ["\\$The Sequence consisting of all elements of seq1, followed by those of seq2."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of both Sequences"]
		++ ["\\#seq1> the first Sequence<br>Has to have the parameter type <i>elemType</i>."]
		++ ["\\#seq2> the second Sequence<br>Has to have the parameter type <i>elemType</i>."];
	append		= ["append object to Sequence"]
		++ ["\\$The Sequence of elements, consisting of all elements of the given Sequence, followed by the given object"]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>seq</i>"]
		++ ["\\#seq The Sequence which should gain <i>object</i>"]
		++ ["\\#object The object of type <i>elemType</i> that is put at the end of <i>seq</i>."];
	prepend		= ["prepend object to Sequence"]
		++ ["\\$The Sequence of elements, consisting of the given object, followed by all elements of the given Sequence"]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>seq</i>"]
		++ ["\\#seq The Sequence which should gain <i>object</i>"]
		++ ["\\#object The object of type <i>elemType</i> that is put at the beginning of <i>seq</i>."];
	subSequence	= ["subsequence"]
		++ ["\\$The subsequence of the given Sequence, starting with the element at the first indes, up to and including the element at the second index"]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>seq</i>"]
		++ ["\\#seq The Sequence from which the subsequence should be taken"]
		++ ["\\#first The index of the first character that should be in the subsequence"]
		++ ["\\#last The index of the last character that should be included in the subsequence"];
	at		= ["element access on sequence"]
		++ ["\\$The element at the position given by the index of the given Sequence"]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>seq</i>"]
		++ ["\\#seq The Sequence from which an element should be taken"]
		++ ["\\#index The number of the element in <i>seq</i> that should be taken<br>The first element in a OCL sequence has index <b>1</b>."];
	first		= ["head of Sequence"]
		++ ["\\$Returns the first element in <i>seq</i>."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>seq</i>"]
		++ ["\\#seq The Sequence from which an element should be taken"];
	last		= ["tail of Sequence"]
		++ ["\\$Returns the last element in <i>seq</i>."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>seq</i>"]
		++ ["\\#seq The Sequence from which an element should be taken"];
	includingSeq	= ["put object at the end of a sequence"]
		++ ["\\$The Sequence of elements, consisting of all elements of the given Sequence, followed by the given object.<br>Identical to <i>append</i>"]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>seq</i>"]
		++ ["\\#seq The Sequence which should gain <i>object</i>"]
		++ ["\\#object The object of type <i>elemType</i> that is put at the end of <i>seq</i>."];
	excludingSeq	= ["put object out of sequence"]
		++ ["\\$The Sequence with the elements of the Sequence but without all occurrences of the object.<br>The order of the remainind elements stays unchanged."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>seq</i>"]
		++ ["\\#seq The Sequence which should loose <i>object</i>"]
		++ ["\\#object The object of type <i>elemType</i>, which is to be removed from <i>seq</i>. <br>That is, if the same object is in the Sequence more than once, all these occurances are removed, not just the first."];
	selectSeq	= ["select from sequence"]
		++ ["\\$The sequence of elements of the Sequence for which the given expression is true.<br>The order of the selected elements stays unchanged."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>seq</i>"]
		++ ["\\#seq The Sequence from which elements are to be seleced. <br>Has to have the parameter type <i>elemType</i>."]
		++ ["\\#body The boolean expression that is the selection predicate, together with the introduction of a bound variable to access each element one at a time"];

	rejectSeq	= ["reject from sequence"]
		++ ["\\$The sequence of elements of the Sequence for which the given expression is false.<br>The order of the not rejected elements stays unchanged."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>seq</i>"]
		++ ["\\#seq The Sequence from which elements are to be seleced. <br>Has to have the parameter type <i>elemType</i>."]
		++ ["\\#body The boolean expression that is the selection predicate, together with the introduction of a bound variable to access each element one at a time"];

	collectSeq	= ["collect results of an expression over a Sequence"]
		++ ["\\$The Sequence of elements that result from applying the given expression to every member of the Sequence."]
		++ ["\\%COLL"]
		++ ["\\#elemType The parameter type of <i>seq</i>"]
		++ ["\\#resultType The type of the result, specified in the expression <i>body</i>."]
		++ ["\\#seq The Set from which the wanted values should be calculated."]
		++ ["\\#body Here it is stated what should be done with each element of <i>seq</i>.<br>This can be a calculation, an attribute access or an arbitrary expression of type <i>resultType</i> together with a bound variable to access each individual element"];
	seqAsBag	= ["sequence as bag"]
		++ ["\\$Returns a Bag that contains all all the elements of the Sequence including duplicates."]
		++ ["\\%COLL"]
		++ ["\\#seqElemType The official element type of <i>seq</i>.<br>That is, the parameter type of <i>seq</i>"]
		++ ["\\#seq The Bag with parameter type <i>seqElemType</i>."];
	seqAsSet	= ["sequence as set"]
		++ ["\\$Returns a Set that contains all all the elements of the Sequence, with duplicates removed."]
		++ ["\\%COLL"]
		++ ["\\#seqElemType The official element type of <i>seq</i>.<br>That is, the parameter type of <i>seq</i>"]
		++ ["\\#seq The Bag with parameter type <i>seqElemType</i>."];
	seqConforms	= ["a collection type conforms to Sequence"]
		++ ["\\$Cast another collection to Sequence"]
		++ ["\\#subtype The parameter type that is a subtype of <i>supertype</i>"]
		++ ["\\#supertype The parameter type that is a supertype of <i>subtype</i>"]
		++ ["\\#inheritance A special proof object, or so-called witness, that is only available for types, for which <i>subtype</i> really is a subtype of <i>supertype</i>."];
	seqConforms2coll= ["upcast Sequence to Collection"]
		++ ["\\$Sequence as a subtype of Collection."]
		++ ["\\#subtype The parameter type that is a subtype of <i>supertype</i>"]
		++ ["\\#supertype The parameter type that is a supertype of <i>subtype</i>"]
		++ ["\\#inheritance A special proof object, or so-called witness, that is only available for types, for which <i>subtype</i> really is a subtype of <i>supertype</i>."];


-- collection literals
lin
	emptySet _ = emptyColl "Set";
	emptySeq _ = emptyColl "Sequence";
	emptyBag _ = emptyColl "Bag";

	singletonSet _ x = singletonColl "Set" x;
	singletonBag _ x = singletonColl "Bag" x;
	singletonSeq _ x = singletonColl "Sequence" x;

printname
	emptySet = ["the empty Set\\%COLL"];
	emptySeq = ["the empty Sequence\\%COLL"];
	emptyBag = ["the empty Bag\\%COLL"];

	singletonSet = ["the Set consisting only ofthe given element\\%COLL"];
	singletonSeq = ["the Sequence consisting only of the given element\\%COLL"];
	singletonBag = ["the Bag consisting only of the given element\\%COLL"];
	

lin
    twoColl _ a b = {s = inst2str a ++ "," ++ inst2str b};
    consColl _ x xs = {s = xs.s ++ "," ++ inst2str x};
    listAsSeq _ xs = listAsColl "Sequence" xs.s;
    listAsSet _ xs = listAsColl "Set" xs.s;
    listAsBag _ xs = listAsColl "Bag" xs.s;

    rangeAsSeq f t = rangeAsColl "Sequence" f t;
    rangeAsSet f t = rangeAsColl "Set" f t;
    rangeAsBag f t = rangeAsColl "Bag" f t;

printname
	twoColl = ["collection-list from 2 elements"]
		++ ["\\%COLL"]
		++ ["\\#type the parameter type of the collection"]
		++ ["\\#!inst1 the first instance in the collection"]
		++ ["\\#!inst2 the other instance in the collection"];
	consColl = ["put instance in a collection-list"]
		++ ["\\%COLL"]
		++ ["\\#type the parameter type of the collection"]
		++ ["\\#!inst the new instance for the collection"]
		++ ["\\#coll the collection-list which should get inst"];
	listAsSeq = ["list of instances for a Sequence"]
		++ ["\\%COLL"]
		++ ["\\#type the parameter type of the Sequence"]
		++ ["\\#coll the collection-list which should be accessed as a Sequence"];
	listAsSet = ["list of instances for a Set"]
		++ ["\\%COLL"]
		++ ["\\#type the parameter type of the Set"]
		++ ["\\#coll the collection-list which should be accessed as a Set"];
	listAsBag = ["list of instances for a Bag"]
		++ ["\\%COLL"]
		++ ["\\#type the parameter type of the Bag"]
		++ ["\\#coll the collection-list which should be accessed as a Bag"];

	rangeAsSeq = ["Integer range as Sequence"]
		++ ["\\%COLL"]
		++ ["\\#from The start of the Integer Sequence"]
		++ ["\\#to The end of the Integer Sequence"];
	rangeAsSet = ["Integer range as Set"]
		++ ["\\%COLL"]
		++ ["\\#from The start of the range of Integers in the Set"]
		++ ["\\#to The end of the range of Integers in the Set"];
	rangeAsBag = ["Integer range as Bag"]
		++ ["\\%COLL"]
		++ ["\\#from The start of the range of Integers in the Bag"]
		++ ["\\#to The end of the range of Integers in the Bag"];
};
