concrete coreOCL of core = open Prelude, externalOperOCL, myTypesOCL, precedenceOCL in {

--# -path=.:../prelude:../abstract

lincat
    Class = ClassL;
    Constraint = ConstraintL;
    Constraints = ConstraintL;
    ConstraintHideContext = ConstraintL;
    Document = DocumentL;
    Instance = Inst;
--    CoercedTo = Inst;
    InstNoType = Inst;
    Sent = Inst;
    AtomSent = Inst;
    AndList = Inst;
    OrList = Inst;
    SumList = Inst;
    ProductList = Inst;
    LetDef = LetDefL;
    LetDefSent = LetDefL;
    LetDefList = LetDefListL;
    InstIter = {s1, s2, s3 : Str};
    SentIter = {s1, s2, s3 : Str};
    Property = PropL;
    Predicate = PropL;


--
-- Sent (should be the same as Instance)
--

lin eq _ = infix eqP "=";
	neq _ = infix eqP "<>";

	negAtom a = prefix unP "not" a;
	posAtom a = a;

printname eq 		= ["=, parametrized equality"]
		++ ["\\$to compare two instances on a specific type"]
		++ ["\\%COMP{comparison operators\\$operators like equality, disequality, greater than, ...}"]
		++ ["\\#class The class/type which both <i>op1</i> and <i>op2</i> must have."]
		++ ["<br>This must be one of the types of <i>op1</i> and <i>op2</i>, just a common supertype is incorrect, but not checked in the grammar."]
		++ ["\\#!op1 The first operand, to be compared with <i>op2</i>"]
		++ ["\\#!op2 The second operand, to be compared with <i>op1</i>"];
printname neq 		= ["<>, parametrized disequality"]
		++ ["\\$to compare two instances on a specific type"]
		++ ["\\%COMP"]
		++ ["\\#class The class/type which both <i>op1</i> and <i>op2</i> must have."]
		++ ["<br>This must be one of the types of <i>op1</i> and <i>op2</i>, just a common supertype is incorrect, but not checked in the grammar."]
		++ ["\\#!op1 The first operand, to be compared with <i>op2</i>"]
		++ ["\\#!op2 The second operand, to be compared with <i>op1</i>"];

printname negAtom 	= ["use a negated AtomSent"]
		++ ["\\%ATOM{atomic sentences\\$boolean model elements and non-standard OCL statements like 'an exception is thrown'<br>These sentences have built-in negated forms to produce nicer natural language rendering, like boolean model elements or thrown exceptions}"]
		++ ["\\#atomSent The atomic sentence like 'an Exception is thrown'"];
printname posAtom 	= ["use an AtomSent"]
		++ ["\\%ATOM"]
		++ ["\\#atomSent The atomic sentence like 'an Exception is thrown'"];
	
--
-- self, result 
--
lin	self _ _ = const "self";
lin	result _ _ = const "result";
printname result 	= ["result"]
		++ ["\\$<html>the result of this operation.<br>Is <b>only</b> allowed in a postcondition</html>"]
		++ ["\\#class The class of the result<br>Filled in automatically"]
		++ ["\\#varResult A special fun that only exists for the right type of the result.<br>Filled in automatically."];
printname self 		= ["self\\$the current instance, often also referred to as 'this'"]
		++ ["\\#class The class of self<br>Filled in automatically"]
		++ ["\\#varSelf A special fun that only exists for the right type of self.<br>Filled in automatically."];

	

--
-- let-definitions
--
lin letProperty rec ret prop definiens = letNoArg rec prop definiens;

    letPredicate = letNoArg;
    
    letAddArg c d boundLetDef = boundLetDef;
    letAddArgSent c boundLetDefSent = boundLetDefSent;

    typeFormalParam clss exp = const ((inst2str exp) ++ ":" ++ clss.s);
    
--     defC c letdef list = ss ("def:" ++ "let" ++ letdef.s0 ++ ":" ++ c.s ++ "=" ++ letdef.s1);
--     defCSent letdef list = ss ("def:" ++ "let" ++ letdef.s0 ++ ":" ++ "Boolean" ++ "=" ++ letdef.s1);
    -- LetDefListL = {s : Bool => Str}; -- each elem in list should be preceeded by either "def:" or "let"
    nilLet = {s = ""; size = E0};
    consLet c ld lds = {
        s = ld.s0 ++ ":" ++ c.s ++ "=" ++ ld.s1 ++ case lds.size of {
            E0 => "";
            _ => "," ++ lds.s
        };
        size = eNext lds.size
    };
    consLetSent ld lds = {
        s = ld.s0 ++ ":" ++ "Boolean" ++ "=" ++ ld.s1 ++ case lds.size of {
            E0 => "";
            _ => "," ++ lds.s
        };
        size = eNext lds.size
    };
    
    localLet lds sent = const ("let" ++ lds.s ++ "in" ++ inst2str sent);

printname
	typeFormalParam = ["get parameter types in OCL linearization of letdefs\\%LET{let definitions}"];

lin
	dropType _ i = i;
-- should we have ["@ pre"] instead of "@pre"?
lin
	atPre _ i = mkAtPre i;
	atPreSent i = mkAtPre i; 

printname
	atPre = ["access value from before the method call (@pre)"]
		++ ["\\$<html>refers to the original value of this property directly before this operation has been called.<br>Is <b>only</b> allowed in a postcondition</html>"]
		++ ["\\#class The class of <i>property</i>"]
		++ ["\\#property The instance of the wanted property.<br><b>Caution:<br><i>Must</i> be a property of a class, although the editor does not enforce this at the moment. "];
	atPreSent = ["access value from before the method call (@pre)"]
		++ ["\\$<html>refers to the original value of this sentence directly before this operation has been called.<br>Is <b>only</b> allowed in a postcondition</html>"]
		++ ["\\#proposition The sentence which should be evaluated at the beginning of the operation.<br> TODO Really in OCL?"];
--
-- Subtyping 
--
lin coerce sub super proof obj = obj;
-- pattern	subTypeRefl c = ["by reflexitivity,"] ++ c ++ ["is a subtype of itself"];
-- 	subTypeTrans a b c proofab proofbc = ["by transitivity,"] ++ a++ ["is a subtype of"] ++
-- 		c ++ ["since"] ++ b ++ ["is a subtype of"] ++ c ++ ["and"] ++ a ++["is a subtype of"] ++ b;

printname coerce = ["upcast"]
		++ ["\\$use a <i>subtype</i> as a <i>supertype</i> if <i>subtype</i> is a subtype of <i>supertype</i><br>This fun is used to eliminate implicit upcasts as in OCL since GF does not support subtyping directly. Has no effect on the linearisation."]
		++ ["\\#subtype the class of the subtype"]
		++ ["\\#supertype the class of the supertype"]
		++ ["\\#proof a special function that only exists, if <i>subtype</i> is indeed a subtype of <i>supertype</i>"]
		++ ["\\#a an instance of <i>subtype</i>"];


--
-- pre- and postconditions
--
lin
	emptyClassC = ss "";
	emptyOperC = ss "";
	emptyPostC = const "true";
	defC c ld list = ss ("def:" ++ ld.s0 ++ ":" ++ c.s ++ "=" ++ ld.s1 ++ list.s);
	defSentC ld list = ss ("def:" ++ ld.s0 ++ ":" ++ "Boolean" ++ "=" ++ ld.s1 ++ list.s);
	preC cond list = ss ("pre:" ++ inst2str cond ++ list.s);
	postC cond list = ss ("post:" ++ inst2str cond ++ list.s);
	prepostCt precond postcond = ss ("pre:" ++ inst2str precond ++ "post:" ++ inst2str postcond);
	invC cond list = ss ("inv:" ++ inst2str cond ++ list.s);
	invCt cond = ss ("inv:" ++ inst2str cond);
	invHC cond = ss (inst2str cond);

printname 
	emptyPostC = ["empty postcondition\\$Use this if an operation should have no postcondition"];
	preC = ["precondition\\$<html>If more than one pre- or postcondition is wanted, use this refinement.<br><b>Caution:</b> This does not work with TogetherCC, but is allowed in the OCL standard."];
	postC = ["postcondition\\$<html>If more than one postcondition is wanted, use this refinement.<br><b>Caution:</b> This does not work with TogetherCC, but is allowed in the OCL standard."];
	prepostCt = ["pre-/postcondition pair for use with TogetherCC"]
		++ ["\\#precondition The precondition for the method. <br>If there should be more than one, conjoin them with <b>and</b>."]
		++ ["\\#postcondition The postcondition for the method. <br>If there should be more than one, conjoin them with <b>and</b>."];
	invC = ["class invariant\\$<html>If more than one invariant is wanted, use this refinement.<br><b>Caution:</b> This does not work with TogetherCC, but is allowed in the OCL standard."];
	invCt = ["class invariant for use with TogetherCC"]
		++ ["\\#invariant The invariant for the class.<br>If there are more than one, they have to be conjoined with <b>and</b>."];


--
-- list of constraints
-- 

lin
	oneConstraint c = c;
	consConstraint c cs = {s = c.s ++ "\\n" ++ cs.s};
	document cs = cs;


printname 
	oneConstraint = ["List of Constraints with size 1\\$<html>Use this to finish a list of constraints<br>><b>Caution:</b> This does not work with TogetherCC where only one constraint is allowed, but is allowed in the OCL standard."];
	consConstraint = ["List of Constraints with size greater than 1\\$<html>Use this to build a list of constraints.<br>This list can be finished with a <i>list of constraints with size 1</i>.<br><b>Caution:</b> This does not work with TogetherCC where only one constraint is allowed, but is allowed in the OCL standard.</html>"];
	document = ["document\\$a document with several constraints for several contexts (classes, operations)"];

--
-- Properties
--
lin
	propCall _ _ obj prop = applyProp prop obj;
	implPropCall _ _ obj prop = applyPropImpl prop obj;
	predCall _ obj prop = applyProp prop obj;
	implPredCall _ obj prop = applyPropImpl prop obj;


printname
	propCall 		= ["normal use of an operation call or attribute access"]
		++ ["\\%MODEL{use model element}"]
		++ ["\\#receiverClass The class of <i>receiver</i>, the class which has the property"]
		++ ["\\#propertyClass The class of the <i>property</i> which should be accessed"]
		++ ["\\#receiver The object of class <i>receiverClass</i> from which the property is accessed."]
		++ ["\\#property The wanted property, be it an attribut or an operation. <br>Note, that Boolean properties cannot be accessed with this function, they are atomic sentences for which special access functions exist."];
	implPropCall 	= ["normal use of an operation call or attribute access (implicit)"]
		++ ["\\$<i>receiver</i> will be omitted in OCL (is implicitly used).<br>Mostly this is for <i>self</i>, but certain collection operations although allow for implicit property calls."]
		++ ["\\%MODEL"]
		++ ["\\#receiverClass The class of <i>receiver</i>, the class which has the property"]
		++ ["\\#propertyClass The class of the <i>property</i> which should be accessed"]
		++ ["\\#receiver The object of class <i>receiverClass</i> from which the property is accessed. <br>This can be either <i>self</i> or an iterator variable introduced by a collection function."]
		++ ["\\#property The wanted property, be it an attribut or an operation. <br>Note, that Boolean properties cannot be accessed with this function, they are atomic sentences for which special access functions exist."];
	predCall 			= ["a boolean property holds for an instance"]
		++ ["\\$To access boolean properties from the model. The result might look light: <br>For <i>receiver</i>, <i><property</i> holds.<br>Or, <i>receiver</i> is something."]
		++ ["\\%MODEL"]
		++ ["\\#receiverClass The class of <i>receiver</i>"]
		++ ["\\#receiver The object from which the property is accessed."]
		++ ["\\#predicate The wanted boolean property"];
	implPredCall 		= ["a boolean property holds, instance can be omitted"]
		++ ["\\$To access boolean properties from the model. For sentences not built with <i>is</i>, <i>receiver</i> is not shown (left implicit).The result might look light: <br><i><property</i> holds.<br>Or, <i>receiver</i> is something."]		++ ["\\%MODEL"]
		++ ["\\#receiverClass The class of <i>receiver</i>"]
		++ ["\\#receiver The object from which the property is accessed. <br>This can be either <i>self</i> or an iterator variable introduced by a collection function."]
		++ ["\\#property The wanted property"];
};
