// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//


/* -*-antlr-*- */
header {
    package de.uka.ilkd.key.speclang.jml.translation;

    import java.io.StringReader;

    import de.uka.ilkd.key.java.JavaInfo;
    import de.uka.ilkd.key.java.Position;
    import de.uka.ilkd.key.java.Services;
    import de.uka.ilkd.key.java.abstraction.*;
    import de.uka.ilkd.key.java.declaration.ArrayDeclaration;
    import de.uka.ilkd.key.java.declaration.ClassDeclaration;
    import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
    import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
    import de.uka.ilkd.key.ldt.AbstractIntegerLDT;
    import de.uka.ilkd.key.ldt.LDT;
    import de.uka.ilkd.key.logic.*;
    import de.uka.ilkd.key.logic.op.*;
    import de.uka.ilkd.key.logic.sort.*;
    import de.uka.ilkd.key.proof.AtPreFactory;
    import de.uka.ilkd.key.proof.OpReplacer;
    import de.uka.ilkd.key.proof.init.CreatedAttributeTermFactory;
    import de.uka.ilkd.key.speclang.FormulaWithAxioms;
    import de.uka.ilkd.key.speclang.PositionedString;
    import de.uka.ilkd.key.speclang.translation.*;
    import de.uka.ilkd.key.util.Debug;

    import java.lang.RuntimeException;
    import java.math.BigInteger;
    import java.util.Map;
    import java.util.LinkedHashMap;
}

class KeYJMLParser extends Parser;
options {
    importVocab=KeYJMLLexer;
    k = 2;
    defaultErrorHandler=false;
}

{
    private static final TermBuilder TB = TermBuilder.DF;
    private static final AtPreFactory APF = AtPreFactory.INSTANCE;

    private Services services;
    private JavaInfo javaInfo;
    private SLTranslationExceptionManager excManager;

    private static Sort boolSort;
    private static Term trueLitTerm;

    private ParsableVariable selfVar;
    private ListOfParsableVariable paramVars;
    private ParsableVariable resultVar;
    private ParsableVariable excVar;
    private Map atPreFunctions;
    
    // Helper objects
    private JMLResolverManager resolverManager;
    private AxiomCollector axiomCollector;
    private JavaIntegerSemanticsHelper intHelper;

    // Helper attributes
    private boolean currentlyParsing = false;
    private static int varCounter = 0;
    
    public KeYJMLParser(TokenStream lexer,
		String fileName,
		Position offsetPos,
		Services services,
		KeYJavaType specInClass,
		AxiomCollector ac,
		ParsableVariable self,
		ListOfParsableVariable paramVars,
		ParsableVariable result,
		ParsableVariable exc,
		/*inout*/ Map /*operator (normal) 
			    -> function (atPre)*/ atPreFunctions) {
	this(lexer);

	// save parameters
	this.services       = services;
	this.javaInfo       = services.getJavaInfo();
	this.excManager     = new SLTranslationExceptionManager(this,
				    fileName, 
				    offsetPos);
	this.axiomCollector = ac;
	this.selfVar	    = self;
	this.paramVars      = paramVars;
	this.resultVar      = result;
	this.excVar	    = exc;
	this.atPreFunctions = atPreFunctions;

	// initialize helper objects
	this.resolverManager = new JMLResolverManager(this.javaInfo,
						      specInClass,
						      selfVar,
						      this.excManager);

	// initialize namespaces
	resolverManager.pushLocalVariablesNamespace();
	if (selfVar != null) {
	    resolverManager.putIntoTopLocalVariablesNamespace(selfVar);
	}
	if (paramVars != null) {
	    IteratorOfParsableVariable it = paramVars.iterator(); 
	    while(it.hasNext()) {
	    resolverManager.putIntoTopLocalVariablesNamespace(it.next());
	    }
	}
	if (resultVar != null) {
	    resolverManager.putIntoTopLocalVariablesNamespace(resultVar);
	}

	this.intHelper = new JavaIntegerSemanticsHelper(services, excManager);

	trueLitTerm = services.getTypeConverter()
	.convertToLogicElement(BooleanLiteral.TRUE);
	boolSort    = services.getJavaInfo()
	.getKeYJavaType(PrimitiveType.JAVA_BOOLEAN)
	.getSort();
    }
    
    
    public KeYJMLParser(PositionedString ps,
		Services services,
		KeYJavaType specInClass,
		AxiomCollector ac,
		ParsableVariable self,
		ListOfParsableVariable paramVars,
		ParsableVariable result,
		ParsableVariable exc,
		/*inout*/ Map /*operator (normal) 
			    -> function (atPre)*/ atPreFunctions) {
	this(new KeYJMLLexer(new StringReader(ps.text)), 
	     ps.fileName, 
	     ps.pos,
	     services,
	     specInClass,
	     ac,
	     self,
	     paramVars,
	     result,
	     exc,
	     atPreFunctions);
    }


    private void raiseError(String msg) throws SLTranslationException {
	throw excManager.createException(msg);
    }
    
    private void raiseError(String msg, Token t) throws SLTranslationException {
	throw excManager.createException(msg, t);
    }
    
    private void raiseNotSupported(String feature) 
	    throws SLTranslationException {
	throw excManager.createWarningException(feature + " not supported"); 
    }
	

    public FormulaWithAxioms parseExpression() throws SLTranslationException {
    
	Term result = null;
	this.currentlyParsing = true;

	try {
	    result = expression();
	} catch (antlr.ANTLRException e) {
	    throw excManager.convertException(e);
	}

	this.currentlyParsing = false;

	return new FormulaWithAxioms(convertToFormula(result), axiomCollector.getAxioms());
    }


    public FormulaWithAxioms parseSignals() throws SLTranslationException {

	Term result = null;
	this.currentlyParsing = true;

	try {
	    result = signalsclause();
	} catch (antlr.ANTLRException e) {
	    throw excManager.convertException(e);
	}

	this.currentlyParsing = false;

	return new FormulaWithAxioms(convertToFormula(result), axiomCollector.getAxioms());
    }


    public FormulaWithAxioms parseSignalsOnly() throws SLTranslationException {

	ListOfKeYJavaType signalsonly = null;
	this.currentlyParsing = true;

	try {
	    signalsonly = signalsonlyclause();
	} catch (antlr.ANTLRException e) {
	    throw excManager.convertException(e);
	}

	this.currentlyParsing = false;

	// Build appropriate term out of the parsed list of types
	// i.e. disjunction of "excVar instanceof ExcType"
	// for every ExcType in the list
	Term result = TB.ff();

	IteratorOfKeYJavaType it = signalsonly.iterator();
	while (it.hasNext()) {
	    KeYJavaType kjt = it.next();
		Function instance
			= kjt.getSort().getInstanceofSymbol(services);
	    result = TB.or( result,
		TB.equals(
		    TB.func(instance, TB.var(this.excVar)),
		    trueLitTerm));
	}

	return new FormulaWithAxioms(result);
    }


    public Term parseAssignable() throws SLTranslationException {
    	Term result = null;

	this.currentlyParsing = true;
	try {
	    result = assignableclause();
	} catch (antlr.ANTLRException e) {
	    throw excManager.convertException(e);
	}
	this.currentlyParsing = false;

	return result;
    }


    public ListOfLogicVariable parseVariableDeclaration() throws SLTranslationException {

	ListOfLogicVariable result = SLListOfLogicVariable.EMPTY_LIST;

	this.currentlyParsing = true;
	try {
	    result = quantifiedvardecls();
	} catch (antlr.ANTLRException e) {
	    throw excManager.convertException(e);
	}
	this.currentlyParsing = false;

	return result;
    }



    /**
     * Extracts a term's subterms as an array.
     */
    private Term[] getSubTerms(Term term) {
	Term[] result = new Term[term.arity()];
	for(int i = 0; i < term.arity(); i++) {
	    result[i] = term.sub(i);
	    assert result[i] != null;
	}
	return result;
    }


    /**
     * Extracts the sorts from an array of terms as an array.
     */
    private Sort[] getSorts(Term[] terms) {
	Sort[] result = new Sort[terms.length];
	for(int i = 0; i < terms.length; i++) {
	    result[i] = terms[i].sort();
	}
	return result;
    }

    /**
     * Converts a term so that all of its non-rigid operators refer to the pre-state.
     * Creates and saves new atPreFunctions when necessary.
     */
    private Term convertToOld(Term term) {
	assert atPreFunctions != null;
	Operator newOp;
	if(!term.op().isRigid() && term.op() != selfVar) {
	    Function atPreFunc = (Function) atPreFunctions.get(term.op());
	    if(atPreFunc == null) {
		atPreFunc = APF.createAtPreFunction(term.op(), services);
		atPreFunctions.put(term.op(), atPreFunc);
		assert atPreFunc != null;
	    }	    
	    newOp = atPreFunc;
	} else {
	    newOp = term.op();
	}
	
	final ArrayOfQuantifiableVariable[] vars = 
		new ArrayOfQuantifiableVariable[term.arity()];
	
	Term[] subTerms = getSubTerms(term);
	Term[] newSubTerms = new Term[subTerms.length];
	for(int i = 0; i < subTerms.length; i++) {
	    newSubTerms[i] = convertToOld(subTerms[i]);
	    vars[i] = term.varsBoundHere(i);
	}
	
	return TB.tf().createTerm(newOp, 
		  		  newSubTerms, 
				  vars, 
				  term.javaBlock());
    }

    private boolean isBoundedSum(Term a, LogicVariable lv){
        return lowerBound(a,lv)!=null && upperBound(a,lv)!=null;
    }
    
    private Term lowerBound(Term a, LogicVariable lv){
        if(a.arity()>0 && a.sub(0).op()==Junctor.AND){
            a=a.sub(0);
        }
        if(a.arity()==2 && a.op()==Junctor.AND && a.sub(0).arity()==2 && a.sub(0).sub(1).op()==lv
                && a.sub(0).op().equals(services.getTypeConverter().getIntegerLDT().getLessOrEquals())){
            return a.sub(0).sub(0);
        }
        return null;
    }
   
    private Term upperBound(Term a, LogicVariable lv){
        if(a.arity()>0 && a.sub(0).op()==Junctor.AND){
            a=a.sub(0);
        }   
        if(a.arity()==2 && a.op()==Junctor.AND && a.sub(1).arity()==2 && a.sub(1).sub(0).op()==lv
                && a.sub(1).op().equals(services.getTypeConverter().getIntegerLDT().getLessThan())){
            return a.sub(1).sub(1);
        }
        return null;
    }


    private String createSignatureString(ListOfTerm signature) {
	if (signature == null || signature.isEmpty()) {
	    return "";
	}
	String sigString = "";
	
	for(IteratorOfTerm it=signature.iterator(); it.hasNext(); ) {
	    sigString += 
		services.getTypeConverter()
		    .getKeYJavaType(it.next()).getFullName() + ", ";
	}
	
	return sigString.substring(0, sigString.length() - 2);
    }
    
    
    private JMLExpression lookupIdentifier(String lookupName,
					   JMLExpression receiver,
					   ListOfTerm callingParameters,
					   Token t)
				       throws SLTranslationException {

	// Identifier with suffix in parantheses? Probably a method call
	// parse in the parameter list and call again
	try {
	    if (LA(1) == LPAREN) {
	    return receiver;
	}
	} catch (TokenStreamException e) {
	    if(currentlyParsing) {
		raiseError("internal Error: no further Token in Stream");
	    }
	}

	ListOfSLExpression paramList = null;
	SLParameters params = null;
	if (callingParameters != null) {
	    paramList = SLListOfSLExpression.EMPTY_LIST;
	    IteratorOfTerm it = callingParameters.iterator();
	    while(it.hasNext()) {
		paramList = paramList.append(new JMLExpression(it.next()));
	    }
	    params = new SLParameters(paramList);
	}
	
	JMLExpression result = (JMLExpression) resolverManager.resolve(
		receiver,
		lookupName,
		params);
	
	if (result != null) {
	    return result;
	}
    
	// no identifier found, maybe it was just a package prefix.
	// but package prefixes don't have a receiver!
	// Let primarysuffix handle faulty method call.
	
	if (receiver != null & callingParameters == null) {
	    raiseError("Identifier " + lookupName + " not found!", t);
	}
	
	return null;
    }


    // If a is a boolean literal, the method returns the literal as a Formula.
    private static Term convertToFormula(Term a) {

	if(a.sort() == boolSort) {
	    return TB.equals(a,trueLitTerm);
	}

	return a;
    }

    private Term buildEqualityTerm(JMLExpression a, JMLExpression b)
	throws SLTranslationException {
    
	if (a.isTerm() && b.isTerm()) {
	    return buildEqualityTerm(a.getTerm(), b.getTerm());
	}
	
	if (a.isType() && b.isType()) {
	    JMLExpression typeofExpr;
	    JMLExpression typeExpr;
	    if(a.getTypeofTerm() != null) {
		typeofExpr = a;
		typeExpr = b;
	    } else {
		if (b.getTypeofTerm() == null) {
		    raiseError("Type equality only supported for expressions " +
			" of shape \"\\typeof(term) == \\type(Typename)\"");
		}
		typeofExpr = b;
		typeExpr = a;
	    }
	    
	    Sort os = typeExpr.getType().getSort();
	    Function ioFunc = os.getExactInstanceofSymbol(services);
	     
	    return TB.equals(
		TB.func(ioFunc, typeofExpr.getTypeofTerm()),
		trueLitTerm);
	}
	
	return null;
    }
    
    
    private Term buildEqualityTerm(Term a, Term b) throws SLTranslationException {

	Term result = null;

	try {
	    if(a.sort() != Sort.FORMULA && b.sort() != Sort.FORMULA) {
		result = TB.equals(a,b);
	    } else {
		result = TB.equiv(convertToFormula(a), convertToFormula(b));
	    }
	} catch (IllegalArgumentException e) {
	    try {
		raiseError("Illegal Arguments in equality expression near " + LT(0));
	    } catch (TokenStreamException tse) {
		System.err.println("No further Token in stream");
		raiseError("Illegal Arguments in equality expression");
	    }
	} catch (TermCreationException e) {
	    raiseError("Error in equality-expression\n" + a.toString() + " == " + b.toString() + ".");
	}

	return result;
    }


//    /**
//     * @param maxmin <code>true</code> for max-Axiom, <code>false</code> for min-Axiom
//     *
//     * See minor thesis "A translation from JML to Java DL" by Christian Engel, p. 40
//     */
//    private Term buildMaxMinAxiom(boolean maxmin, Function y, ListOfLogicVariable qVars, Term pred, Term body) {
//
//	Term result = TB.not(TB.ex(qVars.toArray(), pred));
//
//	ProgramVariable n;
//	String progVarName;
//	String className;
//	if (maxmin) {
//	    progVarName = "MIN_VALUE";
//	} else {
//	    progVarName = "MAX_VALUE";
//	}
//
//	System.out.println();
//	System.out.println(qVars.head().sort().toString());
//	System.out.println();
//
//	if (qVars.head().sort().toString().equals("jlong")) {
//	    className = "java.lang.Long";
//	} else {
//	    className = "java.lang.Integer";
//	}
//
//	n = javaInfo.getAttribute(progVarName, className);
//
//	result = TB.and(result,
//	    TB.equals(
//		TB.func(y),
//		TB.var(n)));
//
//	Term t = TB.func(y);
//
//	if (maxmin) {
//	    t = TB.geq(t,body, services);
//	} else {
//	    t = TB.leq(t,body, services);
//	}
//
//	t = TB.all(qVars.toArray(), TB.imp(pred,t));
//	t = TB.and(
//	    t,
//	    TB.ex(qVars.toArray(),
//		TB.and(
//		    pred,
//		    TB.equals(
//			body,
//			TB.func(y)))));
//
//	result = TB.or(result, t);
//
//	return result;
//  }
    
/*    
    private SetOfLocationDescriptor getObjectCreationModSet(KeYJavaType kjt) {
    	SetOfLocationDescriptor result = SetAsListOfLocationDescriptor.EMPTY_SET;
    	
    	//collect implicit attributes
    	ProgramVariable nextToCreate 
    		= javaInfo.getAttribute(
    				ImplicitFieldAdder.IMPLICIT_NEXT_TO_CREATE, 
    				kjt);
    	ProgramVariable createdAttribute
		= javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_CREATED, 
					javaInfo.getJavaLangObject());
	ProgramVariable initializedAttribute
		= javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_INITIALIZED, 
                                        javaInfo.getJavaLangObject());
	ProgramVariable transientAttribute
		= javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_TRANSIENT, 
                                        javaInfo.getJavaLangObject());
	ProgramVariable objectTimesFinalizedAttribute
		= javaInfo.getAttribute("objectTimesFinalized", 
                                        javaInfo.getJavaLangObject());
        
        //create logic variable, guard
        Sort integerSort 
        	= services.getTypeConverter().getIntegerLDT().targetSort();
        LogicVariable lv 
        	= new LogicVariable(new Name("x"), integerSort);
	Term lvTerm = TB.var(lv);
	Function repos = kjt.getSort().getObjectRepository();
	Term objectTerm = TB.func(repos, lvTerm); 
	Term guardFma = TB.leq(TB.dot(null, nextToCreate), lvTerm, services); 
	
	//<nextToCreate>
	Term nextToCreateTerm = TB.dot(null, nextToCreate);
	BasicLocationDescriptor nextToCreateLd
		= new BasicLocationDescriptor(nextToCreateTerm);
	result = result.add(nextToCreateLd);
		
	//<created>
	Term createdTerm = TB.dot(objectTerm, createdAttribute);
	BasicLocationDescriptor createdLd 
		= new BasicLocationDescriptor(guardFma, createdTerm);
	result = result.add(createdLd);
		
	//<initialized>
	Term initializedTerm = TB.dot(objectTerm, initializedAttribute);
	BasicLocationDescriptor initializedLd
		= new BasicLocationDescriptor(guardFma, initializedTerm);
	result = result.add(initializedLd); 
	
	//<transient>
	Term transientTerm   = TB.dot(objectTerm, transientAttribute);
	BasicLocationDescriptor transientLd
		= new BasicLocationDescriptor(guardFma, transientTerm);
	result = result.add(transientLd);
	
	//objectTimesFinalized (a ghost field in java.lang.Object)
	if(objectTimesFinalizedAttribute != null) {
	    Term objectTimesFinalizedTerm 
			     = TB.dot(objectTerm, objectTimesFinalizedAttribute);
	    BasicLocationDescriptor objectTimesFinalizedLd
		= new BasicLocationDescriptor(guardFma, objectTimesFinalizedTerm);
	    result = result.add(objectTimesFinalizedLd); 
    	}

	//local instance fields of created objects
	if(kjt.getJavaType() instanceof ClassDeclaration) {
		ListOfKeYJavaType kjts = javaInfo.getAllSupertypes(kjt).append(kjt);
        IteratorOfKeYJavaType kit = kjts.iterator();
        while(kit.hasNext()){
            KeYJavaType skjt = kit.next();
            if(skjt.getJavaType() instanceof ClassDeclaration){
                ClassDeclaration cd = (ClassDeclaration)skjt.getJavaType();
	            ListOfField fields = javaInfo.getAllFields(cd);
	            for(IteratorOfField it = fields.iterator(); it.hasNext(); ) {
                    Field f = it.next();
                    ProgramVariable pv = (ProgramVariable) f.getProgramVariable();
                    if(!pv.isStatic()) {
                        Term fieldTerm = TB.dot(objectTerm, pv);
                        BasicLocationDescriptor fieldLd 
                            = new BasicLocationDescriptor(guardFma, fieldTerm);
                        result = result.add(fieldLd);
                    }
                }
            }
        }
	} else {
	    assert kjt.getJavaType() instanceof ArrayDeclaration;
	    
	    //length
	    Term lengthTerm = TB.dot(objectTerm, javaInfo.getArrayLength());
	    BasicLocationDescriptor lengthLd
		= new BasicLocationDescriptor(guardFma, lengthTerm);
	    result = result.add(lengthLd);
	    
	    //slots
	    LogicVariable idxLv 
	    	= new LogicVariable(new Name("idx"), integerSort);
	    Term arrTerm 
	    	= TB.dotArr(services, objectTerm, TB.var(idxLv));
	    BasicLocationDescriptor arrLd
	    	= new BasicLocationDescriptor(guardFma, arrTerm);
	    result = result.add(arrLd);
	}
    	
	return result;
    }    

    
    private Term getObjectCreationFma(KeYJavaType kjt) {
	ProgramVariable nextToCreate 
    		= javaInfo.getAttribute(
    				ImplicitFieldAdder.IMPLICIT_NEXT_TO_CREATE, 
    				kjt);
	Term nextToCreateTerm = TB.dot(null, nextToCreate);
	Term oldNextToCreateTerm = convertToOld(nextToCreateTerm);
	return TB.leq(oldNextToCreateTerm, nextToCreateTerm, services);
    }
*/        
}


top throws SLTranslationException
{
    Term t;
}
:
    t=expression
    { 
	Debug.fail("Should be never entered. Only workaround of an antlr bug."); 
    }
    ;
    

assignableclause returns [Term result = null] throws SLTranslationException
:
    result=storereflist
    ;
    

storereflist returns [Term result = null] throws SLTranslationException
{
    Term mod = null;
}
:
    result=storeref 
	(COMMA mod=storeref { result = TB.union(services, result, mod); } )*
    ;


storeref returns [Term result = null] throws SLTranslationException
:
	result=storerefexpression
    |   LPAREN MULT { raiseNotSupported("informal descriptions"); }
    |   result=storerefkeyword
    ;

storerefexpression returns [Term result = null] throws SLTranslationException
{
    JMLExpression expr;
}
:
    expr=storerefname 
    (
	result=storerefnamesuffix[expr]   { expr = new JMLExpression(result); }
    )*
    {
	if(result == null) {
	    if(services.getTypeConverter().getHeapLDT().getSortOfSelect(expr.getTerm().op()) == null) {
	        raiseError("Something is wrong: " + expr.getTerm());
	    } else {
	        Term objTerm = expr.getTerm().sub(1);
	        Term fieldTerm = expr.getTerm().sub(2);
	    	result = TB.pairSingleton(services, objTerm, fieldTerm);
	    }
	}
    }
    ;exception
        catch [TermCreationException ex] {
              raiseError(ex.getMessage());
        }
    


storerefname returns [JMLExpression result = null] throws SLTranslationException
:
    id:IDENT
    {
	result = lookupIdentifier(id.getText(), null, null, id);
	if(result == null) {
	    raiseError("identifier not found: " + id.getText());
	}
    }
    | SUPER
    {
	raiseNotSupported("location \"super\"");
    }
    | THIS
    {
	result = new JMLExpression(TB.var(selfVar));
    }
    ;
    

storerefnamesuffix[JMLExpression receiver] returns [Term result = null] throws SLTranslationException
:
    DOT id:IDENT
    {
	JMLExpression expr = lookupIdentifier(id.getText(), receiver, null, id);
	if (!expr.isTerm()) {
	    raiseError("Error in store-ref-suffix");
	}
	if(services.getTypeConverter().getHeapLDT().getSortOfSelect(expr.getTerm().op()) == null) {
	    raiseError("Something is wrong.");
	} else {
	    Term objTerm = expr.getTerm().sub(1);
	    Term fieldTerm = expr.getTerm().sub(2);
	    result = TB.pairSingleton(services, objTerm, fieldTerm);
	}
    }
    | DOT THIS
    {
	raiseNotSupported("location \"this\" as store-ref-suffix");
    }
    | LBRACKET result = specarrayrefexpr[receiver] RBRACKET
    | DOT MULT
    {
	result = TB.allFields(services, receiver.getTerm());
    }
    ;

specarrayrefexpr[JMLExpression receiver] returns [Term result = null] throws SLTranslationException
{
    Term rangeFrom=null;
    Term rangeTo=null;
}
:
    (
	( rangeFrom=specexpression (DOTDOT rangeTo=specexpression)? )
	| MULT
    )
    {
        LogicVariable indexVar 
	    = new LogicVariable(
	              new Name("i"), 
		      services.getTypeConverter().getIntegerLDT().targetSort());
	Term arrIndex = TB.arr(services, TB.var(indexVar));

	if (rangeFrom == null) {
	    // We have a star. A star includes all components of an array even
	    // those out of bound. This makes proving easier.	    
	    result = TB.locComprehension(services,
	    				 indexVar, 
	                                 receiver.getTerm(), 
	                                 arrIndex);
	} else if (rangeTo != null) {
	    // We have "rangeFrom .. rangeTo"
	    Term guardFormula 
	    	= TB.and(TB.leq(rangeFrom, TB.var(indexVar), services),
		         TB.leq(TB.var(indexVar), rangeTo, services));
            result = TB.guardedLocComprehension(
	    			services, 
	                        indexVar,
	                        guardFormula,
	                        receiver.getTerm(),
				arrIndex);
	} else {
	    // We have a regular array access
	    result = TB.pairSingleton(services, 
	                              receiver.getTerm(),
	                              TB.arr(services, rangeFrom));
	}
    }
    ;exception
        catch [TermCreationException ex] {
              raiseError(ex.getMessage());
        }


storerefkeyword returns [Term result = null] throws SLTranslationException
{
    KeYJavaType t = null;
}
:
    NOTHING { result = TB.empty(services); }
    | EVERYTHING { result = TB.allLocs(services); }
    | NOT_SPECIFIED { result = TB.allLocs(services); }
;


signalsonlyclause returns [ListOfKeYJavaType result = SLListOfKeYJavaType.EMPTY_LIST] throws SLTranslationException
{
    KeYJavaType t=null;
}
:
	NOTHING
    |   t=referencetype { result = result.append(t); } (COMMA t=referencetype { result = result.append(t); })*
    ;
    
signalsclause returns [Term result=null] throws SLTranslationException
{
    KeYJavaType excType = null;
    Term pred = null;
    String vName = null;
    LogicVariable eVar = null;
}
:
	LPAREN excType=referencetype (id:IDENT { vName = id.getText(); })? RPAREN
	{
	    if (vName != null) {
		eVar = new LogicVariable(new Name(vName), excType.getSort());
		resolverManager.pushLocalVariablesNamespace();
		resolverManager.putIntoTopLocalVariablesNamespace(eVar);
	    }
	}
	(result = predornot)?
	{
	    if (vName != null) {
		resolverManager.popLocalVariablesNamespace();
	    }
	    if (result == null) {
		result = TB.tt();
	    } else {
		Map /* Operator -> Operator */ replaceMap = new LinkedHashMap();
		replaceMap.put(eVar, excVar);
		OpReplacer excVarReplacer = new OpReplacer(replaceMap);
		
		Sort os = excType.getSort();
		Function instance = os.getInstanceofSymbol(services);
		
		result = TB.imp(
		    TB.equals(TB.func(instance, TB.var(excVar)), trueLitTerm),
		    convertToFormula(excVarReplacer.replace(result)));
	    }
	}
    ;

predornot returns [Term result=null] throws SLTranslationException
:
	result=predicate
    |   NOT_SPECIFIED
    |   SAME
    ;
    
predicate returns [Term result=null] throws SLTranslationException
:
	result=specexpression
    ;

specexpression returns [Term result=null] throws SLTranslationException
:
	result=expression
    ;

spec_expression_list returns [ListOfTerm result=SLListOfTerm.EMPTY_LIST] throws SLTranslationException
{
    Term t;
}
:
	t=specexpression {result = result.append(t);} (COMMA t=specexpression {result = result.append(t);})*
    ;

expression returns [Term result=null] throws SLTranslationException
:
	result=assignmentexpr
    ;

assignmentexpr returns [Term result=null] throws SLTranslationException
{
    Term t;
}
:
	result=conditionalexpr
// not used in JML expressions
//	(
//	    assignmentOp t=assignmentexpr
//	)?
    ;

	
conditionalexpr returns [Term result=null] throws SLTranslationException
{
    Term a,b;
}
:
	result=equivalenceexpr 
	(
	    QUESTIONMARK a=conditionalexpr COLON b=conditionalexpr
	    {
		result = TB.ife(convertToFormula(result),a,b);
		if(intHelper.isIntegerTerm(result)) {
		    result = intHelper.castToLDTSort(result, 
					             services.getTypeConverter()
					                     .getIntLDT());
		}
	    }
	)?
    ;

equivalenceexpr returns [Term result=null] throws SLTranslationException
{
    Term t;
}
:
	result=impliesexpr 
	(
	    EQV t=equivalenceexpr
	    {
		result = buildEqualityTerm(result,t);
	    } 
	    
	|
	    ANTIV t=equivalenceexpr
	    {
		t = buildEqualityTerm(result,t);
		result = TB.not(t);
	    } 
	    
	)?
    ;
	
impliesexpr returns [Term result=null] throws SLTranslationException
{
    Term t;
}
:
	result=logicalorexpr 
	(
	    IMPLIES t=impliesnonbackwardexpr
	    {
		result = TB.imp(convertToFormula(result),convertToFormula(t));
	    }
	    
	  |
	    (
		IMPLIESBACKWARD t=logicalorexpr
		{
		    result = TB.imp(convertToFormula(t),convertToFormula(result));
		}
	    )+
	)?
;

impliesnonbackwardexpr returns [Term result=null] throws SLTranslationException
{
    Term t;
}
:
	result=logicalorexpr
	(
	    IMPLIES t=impliesnonbackwardexpr
	    {
		result = TB.imp(convertToFormula(result),convertToFormula(t));
	    }
	)?
;	

logicalorexpr returns [Term result=null] throws SLTranslationException
{
    Term t;
}
:
	result=logicalandexpr
	(
	    LOGICALOR t=logicalorexpr
	    {
		result = TB.or(convertToFormula(result), convertToFormula(t));
	    }
	)?
;

logicalandexpr returns [Term result=null] throws SLTranslationException
{
    Term t;
}
:
	result=inclusiveorexpr
	(
	    LOGICALAND t=logicalandexpr
	    {
		result = TB.and(convertToFormula(result), convertToFormula(t));
	    }
	)?
;


inclusiveorexpr returns [Term result=null] throws SLTranslationException
{
    Term t;
}
:
	result=exclusiveorexpr 
	(
	    INCLUSIVEOR t=inclusiveorexpr
	    {
	       if(intHelper.isIntegerTerm(result)) {
                   result = intHelper.buildPromotedOrExpression(result,t);
               } else {
                   result = TB.or(convertToFormula(result), convertToFormula(t));
               }
	    }
	)?
;


exclusiveorexpr returns [Term result=null] throws SLTranslationException
{
    Term t;
}
:
	result=andexpr 
	(
	    XOR t=exclusiveorexpr
	    {
	       if(intHelper.isIntegerTerm(result)) {
                   result = intHelper.buildPromotedXorExpression(result,t);
               } else {
                   Term resultFormula = convertToFormula(result);
                   Term tFormula = convertToFormula(t);
                   result = TB.or(TB.and(resultFormula, TB.not(tFormula)), 
                                  TB.and(TB.not(resultFormula), tFormula));
               }
	    }
	)?
;


andexpr returns [Term result=null] throws SLTranslationException
{
    JMLExpression left;
    Term t;
}
:
	left=equalityexpr
	{
	    if(!left.isTerm()) {
		raiseError("Found a type where only a term is allowed: " 
			   + left);
	    }
	    result = left.getTerm();
	}
	(
	    AND t=andexpr
	    { 
	       if(intHelper.isIntegerTerm(result)) {
                   result = intHelper.buildPromotedAndExpression(result,t);
               } else {
                   result = TB.and(convertToFormula(result), convertToFormula(t));
               }
	    }
	)?
;


equalityexpr returns [JMLExpression result=null] throws SLTranslationException
{
    JMLExpression right;
}
:
	result=relationalexpr 
	(
	    eq: EQUAL right=equalityexpr
	    {
		if (result.isType() ^ right.isType()) {
		    raiseError("Cannot build equality expression between term " +
			"and type.", eq);
		}
		result = new JMLExpression(buildEqualityTerm(result, right));
	    }
	|
	    ne: NOTEQUAL right=equalityexpr
	    {
		if (result.isType() ^ right.isType()) {
		    raiseError("Cannot build equality expression between term " +
			"and type.", ne);
		}
		result = new JMLExpression(TB.not(buildEqualityTerm(result, right)));
	    }
	    
	)?
;

relationalexpr returns [JMLExpression result=null] throws SLTranslationException
{
    Function f = null;
    KeYJavaType type = null;
    JMLExpression right = null;
    Token opToken = null;
}
:
	result=shiftexpr
	(
	    lt:LT right=shiftexpr 
	    {
		f = services.getTypeConverter().getIntegerLDT().getLessThan();
		opToken = lt;
	    }
	|
	    gt:GT right=shiftexpr
	    {
		f = services.getTypeConverter().getIntegerLDT().getGreaterThan();
		opToken = gt;
	    }
	|
	    leq:LEQ right=shiftexpr
	    {
		f = services.getTypeConverter().getIntegerLDT().getLessOrEquals();
		opToken = leq;
	    }
	|
	    geq:GEQ right=shiftexpr
	    {
		f = services.getTypeConverter().getIntegerLDT().getGreaterOrEquals();
		opToken = geq;
	    }
	|
	    io:INSTANCEOF type=typespec 
	    {
		f = type.getSort().getInstanceofSymbol(services);
		opToken = io;
	    }
	|
	    st:ST right=shiftexpr
	    {
		if (result.isTerm() || right.isTerm()) {
		    raiseError("Cannot build subtype expression from terms.", st);
		}
		assert result.isType();
		assert right.isType();
		
		if (result.getTypeofTerm() == null) {
		    raiseError("subtype expression <: only supported for" +
			" \\typeof() arguments on the left side.", st);
		}
		
		Sort os = right.getType().getSort();
		Function ioFunc = os.getInstanceofSymbol(services);
		
		result = new JMLExpression(
		    TB.equals(
			TB.func(ioFunc, result.getTypeofTerm()),
			trueLitTerm));
	    }
	)?
	{
	    if (f != null) {
		assert opToken != null;
		if (result.isType()) {
		    raiseError("Cannot build relational expression from type " +
			result.getType().getName() + ".", opToken);
		}
		assert result.isTerm();
		
		try {
			if (right == null) {
			    // instanceof-expression
			    result = new JMLExpression(
				TB.func(f, result.getTerm()));
			} else {
			    if (right.isType()) {
			    raiseError("Cannot build relational expression from type " +
				right.getType().getName() + ".", opToken);
			    }
			    assert right.isTerm();
			    
			    result = new JMLExpression(
				TB.func(f,result.getTerm(),right.getTerm()));
			}
		} catch (TermCreationException e) {
		    raiseError("Error in relational expression.");
		} catch (IllegalArgumentException e) {
		    raiseError("Internal error.");
		}
	    }
	}
;

shiftexpr returns [JMLExpression result=null] throws SLTranslationException
{
    JMLExpression e;
}
:
    result=additiveexpr
    (
	SHIFTRIGHT e=additiveexpr
	{
	    if (result.isType()) {
		raiseError("Cannot build shift expression from type " +
		    result.getType().getName() + ".");
	    }
	    if (e.isType()) {
		raiseError("Cannot shift right by type " +
		    e.getType().getName() + ".");
	    }
	    assert result.isTerm();
	    assert e.isTerm();

	    result = new JMLExpression(
		intHelper.buildRightShiftExpression(result.getTerm(),e.getTerm()));
	}
    |   
	SHIFTLEFT e=additiveexpr 
	{
	    if (result.isType()) {
		raiseError("Cannot build shift expression from type " +
		    result.getType().getName() + ".");
	    }
	    if (e.isType()) {
		raiseError("Cannot shift left by type " +
		    e.getType().getName() + ".");
	    }
	    assert result.isTerm();
	    assert e.isTerm();

	    result = new JMLExpression(
		intHelper.buildLeftShiftExpression(result.getTerm(),e.getTerm()));
	}
    |   
	UNSIGNEDSHIFTRIGHT e=additiveexpr 
	{
	    if (result.isType()) {
		raiseError("Cannot build shift expression from type " +
		    result.getType().getName() + ".");
	    }
	    if (e.isType()) {
		raiseError("Cannot shift right (unsigned) by type " +
		    e.getType().getName() + ".");
	    }
	    assert result.isTerm();
	    assert e.isTerm();

	    result = new JMLExpression(
		intHelper.buildUnsignedRightShiftExpression(result.getTerm(),e.getTerm()));
	}
    )*
; 


additiveexpr returns [JMLExpression result=null] throws SLTranslationException
{
    JMLExpression e;
}
:
    result=multexpr
    (
	PLUS e=multexpr
	{
	    if (result.isType()) {
		raiseError("Cannot build additive expression from type " +
		    result.getType().getName() + ".");
	    }
	    if (e.isType()) {
		raiseError("Cannot add type " +
		    e.getType().getName() + ".");
	    }
	    assert result.isTerm();
	    assert e.isTerm();

	    result = new JMLExpression(
		intHelper.buildAddExpression(result.getTerm(),e.getTerm()));
	}
    |
	MINUS e=multexpr
	{
	    if (result.isType()) {
		raiseError("Cannot build additive expression from type " +
		    result.getType().getName() + ".");
	    }
	    if (e.isType()) {
		raiseError("Cannot subtract type " +
		    e.getType().getName() + ".");
	    }
	    assert result.isTerm();
	    assert e.isTerm();

	    result = new JMLExpression(
		intHelper.buildSubExpression(result.getTerm(),e.getTerm()));
	}
    )*
;


multexpr returns [JMLExpression result=null] throws SLTranslationException
{
    JMLExpression e;
}
:
    result=unaryexpr
    (
	MULT e=unaryexpr
	{
	    if (result.isType()) {
		raiseError("Cannot build multiplicative expression from type " +
		    result.getType().getName() + ".");
	    }
	    if (e.isType()) {
		raiseError("Cannot multiply by type " +
		    e.getType().getName() + ".");
	    }
	    assert result.isTerm();
	    assert e.isTerm();
	
	    result = new JMLExpression(
		intHelper.buildMulExpression(result.getTerm(),e.getTerm()));
	}
    |
	DIV e=unaryexpr
	{
	    if (result.isType()) {
		raiseError("Cannot build multiplicative expression from type " +
		    result.getType().getName() + ".");
	    }
	    if (e.isType()) {
		raiseError("Cannot divide by type " +
		    e.getType().getName() + ".");
	    }
	    assert result.isTerm();
	    assert e.isTerm();

	    result = new JMLExpression(
		intHelper.buildDivExpression(result.getTerm(),e.getTerm()));
	}
    |
	MOD e=unaryexpr
	{
	    if (result.isType()) {
		raiseError("Cannot build multiplicative expression from type " +
		    result.getType().getName() + ".");
	    }
	    if (e.isType()) {
		raiseError("Cannot build modulo expression from type " +
		    e.getType().getName() + ".");
	    }
	    assert result.isTerm();
	    assert e.isTerm();

	    result = new JMLExpression(
		intHelper.buildModExpression(result.getTerm(),e.getTerm()));
	}
    )*
;


unaryexpr returns [JMLExpression result=null] throws SLTranslationException
{
    KeYJavaType type = null;
}
:
(
       PLUS result=unaryexpr
	{
	    if (result.isType()) {
		raiseError("Cannot build  +" + result.getType().getName() + ".");
	    }
	    assert result.isTerm();
	    
	    result = new JMLExpression(
		intHelper.buildPromotedUnaryPlusExpression(result.getTerm()));
	}
    |
	MINUS result=unaryexpr
	{
	    if (result.isType()) {
		raiseError("Cannot build  -" + result.getType().getName() + ".");
	    }
	    assert result.isTerm();

	    result = new JMLExpression(
		intHelper.buildUnaryMinusExpression(result.getTerm()));
	}
    |
	(LPAREN typespec RPAREN ) => 
	   LPAREN type=typespec RPAREN result=unaryexpr
	
    |
	result=unaryexprnotplusminus
)
	 {
	     if (type != null) {
		 if (result.isType()) {
		     raiseError("Casting of type variables not (yet) supported.");
		 }
		 assert result.isTerm();

		 if (!(type.getSort() instanceof AbstractSort)) {
		     raiseError("Wrong type argument in cast expression.");
		 }
		 
		 Term resultTerm = result.getTerm(); 
		 Function castFunction;
		 if (type.getSort().extendsTrans(services.getTypeConverter().
		    getIntegerLDT().targetSort())) {
		      castFunction = ((AbstractIntegerLDT)services.getTypeConverter().
			getModelFor(type.getSort())).getCast();	
		    resultTerm = TB.func(castFunction, resultTerm);
		 } 
		 
		 castFunction = ((AbstractSort) type.getSort()).getCastSymbol(services);
		 
		 
		 result = new JMLExpression(
		     TB.func(castFunction, resultTerm));
	     }
	}
;


unaryexprnotplusminus returns [JMLExpression result=null] throws SLTranslationException
{
    JMLExpression e;
}
:
	NOT e=unaryexpr
	{
	    if (e.isType()) {
		raiseError("Cannot negate type " + e.getType().getName() + ".");
	    }
	    
	    Term t = e.getTerm();
	    assert t != null;
	    
	    if (t.sort() == Sort.FORMULA) {
		result = new JMLExpression(TB.not(t));
	    } else if (t.sort() == boolSort) {
		result = new JMLExpression(TB.not(TB.equals(t,trueLitTerm)));
	    } else {
		raiseError("Wrong type in not-expression: " + t);
	    }
	}
    |   
	BITWISENOT e=unaryexpr
	{
	    if (e.isType()) {
		raiseError("Cannot negate type " + e.getType().getName() + ".");
	    }
		
	    result = new JMLExpression(
			 intHelper.buildPromotedNegExpression(e.getTerm()));
	}
	
    |
	result=postfixexpr
;


postfixexpr returns [JMLExpression result=null] throws SLTranslationException
{
    String fullyQualifiedName = "";
    JMLExpression expr = null;
}
:
	expr=primaryexpr
	{
	    fullyQualifiedName = LT(0).getText();
	}
	(
	    {
		if (expr != null && expr.getKeYJavaType(javaInfo).getJavaType() instanceof PrimitiveType) {
		    raiseError("Cannot build postfix expression from primitive type.");
		}
	    }
	    expr=primarysuffix[expr, fullyQualifiedName]
	    {
		fullyQualifiedName += "." + LT(0).getText();
	    }
	)*
	
	{
	    if (expr == null) {
		raiseError("Expression " + fullyQualifiedName + " cannot be resolved.");
	    }
	    result = expr; //.getTerm();
	}
	    
;

primaryexpr returns [JMLExpression result=null] throws SLTranslationException
{
    Term t;
}
:
	t=constant   { result = new JMLExpression(t); }
    |   id:IDENT     { result = lookupIdentifier(id.getText(), null, null, id); }
    |   TRUE         { result = new JMLExpression(TB.tt()); }
    |   FALSE        { result = new JMLExpression(TB.ff()); }
    |   NULL         { result = new JMLExpression(TB.NULL(services)); }
    |   result=jmlprimary 
    |   THIS       
        { 
            if(selfVar == null) {
            	raiseError("Cannot access \"this\" in a static context!"); 
            }
            result = new JMLExpression(TB.var(selfVar));
        }
    |   new_expr
;   

primarysuffix[JMLExpression receiver, String fullyQualifiedName] returns [JMLExpression result=null] throws SLTranslationException
{
    Term t;
    String lookupName = null;
    
    ListOfTerm callingParameters = SLListOfTerm.EMPTY_LIST;
}
:
{
    lookupName = fullyQualifiedName;
}
(
	DOT id:IDENT
	{
	    if (receiver == null) {
		// Receiver was only a package/classname prefix
		lookupName = fullyQualifiedName + "." + id.getText();
	    } else {
		lookupName = id.getText();
	    }
	    try{
	    	result = lookupIdentifier(lookupName, receiver, null, id);
	    }catch(SLTranslationException e){
	    	result = lookupIdentifier(fullyQualifiedName + "." + lookupName, null, null, id);
	    }
	}
    |
    DOT THIS
    {
    	result = new JMLExpression(services.getTypeConverter().findThisForSort(receiver.getSort(),
    		TB.var(selfVar), javaInfo.getKeYJavaType(selfVar.sort()), true));
    }
    |
	l:LPAREN (callingParameters=expressionlist)? RPAREN
	{
/*
	    System.out.println("Looking up: " + lookupName);
	    System.out.println("method lookup with parameters:");
	    System.out.println(callingParameters.toString());
	    System.out.println("and receiver: " + receiver);
	    System.out.println();
*/
	    result = lookupIdentifier(lookupName, receiver, callingParameters, l);
	    if (result == null) {
		// method calls must result in an object!
		raiseError("Method " + lookupName + "("
		    + createSignatureString(callingParameters) + ") not found!",l);
	    }
	}
    |
	lbrack:LBRACKET t=expression RBRACKET
	{
	    if (receiver == null) {
		raiseError("Array \"" + fullyQualifiedName + "\" not found.", lbrack);
	    }
	    if (receiver.isType()) {
		raiseError("Error in array expression: \"" + fullyQualifiedName +
		    "\" is a type.", lbrack);
	    }
	    
	    try {
		    result = new JMLExpression(TB.dotArr(services, receiver.getTerm(),t));
	    } catch (TermCreationException e) {
		raiseError(e.getMessage());
	    } catch (IllegalArgumentException e) {
		raiseError(e.getMessage());
	    }
	}
)	
;

new_expr throws SLTranslationException
{
    KeYJavaType typ = null;
}
:
	NEW typ=type new_suffix
        {	
        	raiseNotSupported("'new' within specifications"); 
        }
    ;

new_suffix throws SLTranslationException
{
    ListOfTerm terms;
}
:
	LPAREN ( terms=expressionlist )? RPAREN 
    ;

expressionlist returns [ListOfTerm result=SLListOfTerm.EMPTY_LIST] throws SLTranslationException
{ 
    Term t;
}
:
	t=expression { result = result.append(t); } (COMMA t=expression {result = result.append(t);} )* 
;

constant returns [Term result=null] throws SLTranslationException
:
	result=javaliteral
;

javaliteral returns [Term result=null] throws SLTranslationException
:
	result=integerliteral
    |
	STRING_LITERAL 
	{
	    raiseNotSupported("string literals");
	}
    |
	CHAR_LITERAL 
	{
	    raiseNotSupported("character literals");
	}
    ;

integerliteral returns [Term result=null] throws SLTranslationException
:
	result=decimalintegerliteral
    |
	result=hexintegerliteral
;

hexintegerliteral returns [Term result=null] throws SLTranslationException
:
    n:HEXNUMERAL
    {
	BigInteger decInteger = new BigInteger(n.getText(),16);
	Term intTerm = TB.zTerm(services,decInteger.toString());
	result = intHelper.castToLDTSort(intTerm, 
					 services.getTypeConverter()
					         .getIntLDT());
    }
;

decimalintegerliteral returns [Term result=null] throws SLTranslationException
:
	result=decimalnumeral
;

decimalnumeral returns [Term result=null] throws SLTranslationException
:
    n:DIGITS
    {
	Term intTerm = TB.zTerm(services,n.getText());
	result = intHelper.castToLDTSort(intTerm, 
					 services.getTypeConverter()
					     	 .getIntLDT());
    }
;

jmlprimary returns [JMLExpression result=null] throws SLTranslationException
{
    Term t;
    ListOfTerm sl;
    KeYJavaType typ;
}
:
	RESULT
	{
	    if (resultVar==null) {
		raiseError("\\result used in wrong context");
	    }
	    result = new JMLExpression(TB.var(resultVar));
	}
    |
	(LPAREN QUANTIFIER) => t=specquantifiedexpression
	{
	    result = new JMLExpression(t);
	}
    |
    (LPAREN BSUM) => t=bsumterm
	{
	    result = new JMLExpression(t);
	}
    |
	(OLD | PRE) LPAREN t=specexpression RPAREN
	{
	    if (atPreFunctions == null) {
		raiseError("JML construct " +
			   "\\old not allowed in this context.");
	    }
	    
	    result = new JMLExpression(convertToOld(t));
	}
    |   
	CREATED LPAREN t=specexpression RPAREN
	{
	    if (t.sort().extendsTrans(services.getJavaInfo().objectSort())) {
		result = new JMLExpression(
		    CreatedAttributeTermFactory.INSTANCE.
			createCreatedTerm(services, t));
	    } else {
		raiseError("\\created only allowed for reference types.");
	    }
	}
	
    |
	NONNULLELEMENTS LPAREN t=specexpression RPAREN
	{
	    Term resTerm = TB.not(TB.equals(t, TB.NULL(services)));

	    if (t.sort() instanceof ArraySort) {
		LogicVariable i = new LogicVariable(new Name("i"), javaInfo
				.getKeYJavaType(PrimitiveType.JAVA_INT)
				.getSort());

		// See JML reference manual
		// http://www.cs.iastate.edu/~leavens/JML/jmlrefman/jmlrefman_11.html#SEC139		
		Term range = TB.and(
		    TB.leq(TB.zero(services), TB.var(i), services),
		    TB.leq(TB.var(i), TB.dotLength(services, t), services));
		Term body = TB.equals(
		    TB.dotArr(services, t, TB.var(i)),
		    TB.NULL(services));
		body = TB.not(body);
		body = TB.imp(range, body);

		result = new JMLExpression(TB.and(resTerm, TB.all(i, body)));
	    }
	}
	
    |   INFORMAL_DESCRIPTION 
	{
	    raiseNotSupported("informal predicates");
	}
//    |   NOT_MODIFIED LPAREN storereflist RPAREN 
	
    |   FRESH LPAREN sl=spec_expression_list RPAREN
	{
	    assert false : "not implemented";
/*	    if (atPreFunctions == null) {
                raiseError("JML construct " +
                    "\\fresh not allowed in this context.");
	    }
    	ProgramVariable createdAttribute
            = javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_CREATED, 
					javaInfo.getJavaLangObject());
        AttributeOp ao = AttributeOp.getAttributeOp(createdAttribute);
        Function atPreFunc = (Function) atPreFunctions.get(ao);
	    if(atPreFunc == null) {
                atPreFunc = APF.createAtPreFunction(ao, services);
                atPreFunctions.put(ao, atPreFunc);
                assert atPreFunc != null;
	    }	    
	    t = TB.tt();
        IteratorOfTerm it = sl.iterator();
        while(it.hasNext()){
            Term n = it.next();
            Term fn = TB.and(TB.not(TB.equals(n, TB.NULL(services))), TB.equals(TB.func(atPreFunc, n), TB.FALSE(services)));
            t = TB.and(t, fn);
        }
        result = new JMLExpression(t);
*/
	} 
	
    |   REACH LPAREN t=specexpression RPAREN
	{
	    raiseNotSupported("\\reach");
	} 
	
    |   DURATION LPAREN t=expression RPAREN 
	{
	    raiseNotSupported("\\duration");
	} 
	
    |   SPACE LPAREN t=specexpression RPAREN
	{
	    raiseNotSupported("\\space");
	} 
	
    |   WORKINGSPACE LPAREN t=expression RPAREN
	{
	    raiseNotSupported("\\working_space");
	} 
	
    |   TYPEOF LPAREN t=specexpression RPAREN
	{
	    result = new JMLExpression(services.getTypeConverter().getKeYJavaType(t),t);
	} 
	
    |   ELEMTYPE LPAREN t=specexpression RPAREN 
	{
	    raiseNotSupported("\\elemtype");
	} 
	
    |   TYPE_SMALL LPAREN typ=typespec RPAREN 
	{
	    result = new JMLExpression(typ);
	} 
	
    |   LOCKSET
	{
	    raiseNotSupported("\\lockset");
	} 
	
    |   IS_INITIALIZED LPAREN typ=referencetype RPAREN 
	{
	    Term resTerm = TB.equals(
		TB.var(
		    javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED, 
					  typ)),
		TB.TRUE(services));
	    result = new JMLExpression(resTerm);
	} 
	
    |   INVARIANT_FOR LPAREN t=specexpression RPAREN 
	{
	    raiseNotSupported("\\invariant_for");
	} 
	
    |   ( LPAREN LBLNEG ) => LPAREN LBLNEG IDENT t=specexpression RPAREN
	{
	    result = new JMLExpression(t);
//	    raiseNotSupported("\\lblneg");
	} 
	
    |   ( LPAREN LBLPOS ) => LPAREN LBLPOS IDENT t=specexpression RPAREN 
	{
	    result = new JMLExpression(t);
//	    raiseNotSupported("\\lblpos");
	} 
	
    |
	NOWARN 
	{
	    raiseNotSupported("\\nowarn");
	} 

    |   LPAREN t=expression RPAREN
	{
	    result = new JMLExpression(t);
	}
;

specquantifiedexpression returns [Term result = null] throws SLTranslationException
{
    Term t = null;
    Term p = TB.tt();
    boolean nullable = false;
    ListOfLogicVariable declVars = null;
}
:
	LPAREN
	q:QUANTIFIER (nullable=boundvarmodifiers)? declVars=quantifiedvardecls SEMI
	
	{
	    resolverManager.pushLocalVariablesNamespace();
	    resolverManager.putIntoTopLocalVariablesNamespace(declVars);
	} 
	(
	    ((predicate)? SEMI ) => (p=predicate)? SEMI t=specexpression
	|
	    (SEMI)? t=specexpression 
	)
	
	{
	    resolverManager.popLocalVariablesNamespace();
	    
	    p = convertToFormula(p);
	    t = convertToFormula(t);
	    
	    //add implicit "non-null" guards for reference types, 
	    //"in-bounds" guards for integer types
	    Term nullTerm = TB.NULL(services);
	    for(IteratorOfLogicVariable it = declVars.iterator(); 
	        it.hasNext(); ) {
	        LogicVariable lv = it.next();
	        
	    	if(lv.sort().extendsTrans(services.getJavaInfo().objectSort()) && !nullable) {
		    p = TB.and(p, TB.not(TB.equals(TB.var(lv), nullTerm)));
		} else {
	    	    LDT ldt 
	    	    	= services.getTypeConverter().getModelFor(lv.sort());
		    if(ldt instanceof AbstractIntegerLDT) {
	    		Function inBounds 
	    			= ((AbstractIntegerLDT) ldt).getInBounds();
	    	    	p = TB.and(p, TB.func(inBounds, TB.var(lv)));
	    	    }
	    	}
	    }	    
	    	    
	    if (q.getText().equals("\\forall")) {
		if (p != null) {
		    t = TB.imp(p, t);
		}
		result = TB.all(declVars.toArray(), t);
	    }
	    else if (q.getText().equals("\\exists")) {
		if (p != null) {
		    t = TB.and(p, t);
		}
		result = TB.ex(declVars.toArray(), t);
	    }
	    else if (q.getText().equals("\\min")) {
	    	raiseNotSupported("\\min");
//		Function y = new RigidFunction(
//		    new Name("_jml_ymin"+(varCounter++)),
//		    declVars.head().sort(),
//		    new Sort[] {});
//		axiomCollector.collectAxiom(y,
//		    buildMaxMinAxiom(false, y, declVars, p, t));
//		result = TB.func(y);
//		services.getNamespaces().functions().addSafely(y);
	    }
	    else if (q.getText().equals("\\max")) {
	        raiseNotSupported("\\max");
//		Function y = new RigidFunction(
//		    new Name("_jml_ymax"+(varCounter++)),
//		    declVars.head().sort(),
//		    new Sort[] {});
//		axiomCollector.collectAxiom(y,
//		    buildMaxMinAxiom(true, y, declVars, p, t));
//		result = TB.func(y);
//		services.getNamespaces().functions().addSafely(y);
	    }
	    else if (q.getText().equals("\\num_of")) {
            LogicVariable lv = declVars.head();
            p=p.sub(0);
            if(p!=null && isBoundedSum(p, lv) && p.sub(0).op()!=Junctor.AND){
                result = TermFactory.DEFAULT.createBoundedNumericalQuantifierTerm(BoundedNumericalQuantifier.BSUM, 
                        lowerBound(p, lv), upperBound(p, lv), TB.ife(
                                t, TB.zTerm(services, "1"), TB.zTerm(services, "0")),
                                new ArrayOfQuantifiableVariable(lv));                          
            }else{
                raiseError("only \\num_of expressions of form (\\sum int i; l<=i && i<u; t) are permitted");
            }
	    }
	    else if (q.getText().equals("\\product")) {
		raiseNotSupported("\\product");
	    }
	    else if (q.getText().equals("\\sum")) {
            LogicVariable lv = declVars.head();
            p=p.sub(0);
            if(isBoundedSum(p, lv)){
                if(p.arity()>0 && p.sub(0).op()==Junctor.AND){
                    t = TB.ife(p.sub(1), t, TB.zTerm(services, "0"));
                }
                result = TermFactory.DEFAULT.createBoundedNumericalQuantifierTerm(BoundedNumericalQuantifier.BSUM, 
                        lowerBound(p, lv), upperBound(p, lv), t, new ArrayOfQuantifiableVariable(lv));
            }else{
                raiseError("only \\sum expressions of form (\\sum int i; l<=i && i<u; t) are permitted");
            }

	    }
	    else {
		raiseError("Unknown quantifier: " + q.getText() + "!");
	    }
	}
	RPAREN
;

bsumterm returns [Term t=null] throws SLTranslationException
{
    Term a=null,b=null; 
    ListOfLogicVariable decls=null;
}:
        LPAREN
        q:BSUM decls=quantifiedvardecls 
        {	    
            resolverManager.pushLocalVariablesNamespace();
            resolverManager.putIntoTopLocalVariablesNamespace(decls);
        } 
        SEMI
        (
            a=specexpression SEMI  b=specexpression SEMI t=specexpression
        )
        {
            LogicVariable lv = (LogicVariable) decls.head();
            t = TermFactory.DEFAULT.createBoundedNumericalQuantifierTerm(BoundedNumericalQuantifier.BSUM, 
                        a, b, t, new ArrayOfQuantifiableVariable(lv));
            resolverManager.popLocalVariablesNamespace();
        }
        RPAREN
;

exception
        catch [SLTranslationException ex] {
        resolverManager.popLocalVariablesNamespace();
        throw ex;
        }   

quantifiedvardecls returns [ListOfLogicVariable vars = SLListOfLogicVariable.EMPTY_LIST] throws SLTranslationException
{
    KeYJavaType t = null;
    LogicVariable v = null;
}
:
	t=typespec v=quantifiedvariabledeclarator[t] 
	
	{ vars = vars.append(v); }
	
	(
	    COMMA v=quantifiedvariabledeclarator[t]
	    
	    { vars = vars.append(v); }
	)*
;

boundvarmodifiers returns [boolean nullable = false] throws SLTranslationException
:
	NON_NULL | NULLABLE { nullable = true; }
;

typespec returns [KeYJavaType t = null] throws SLTranslationException
{
    int dim = 0;
}
:
	t=type 
	(
	    dim=dims
	    {
		String fullName = t.getFullName();
		for (int i=0; i < dim; i++) {
		    fullName += "[]";
		}
		t = javaInfo.getKeYJavaType(fullName);
	if(t == null && dim > 0) {
	    //try to create missing array type
	      try {
	    javaInfo.readJavaBlock("{" + fullName + " k;}");
	    t = javaInfo.getKeYJavaType(fullName);
	    } catch (Exception e) {
	    t = null;
		}
	    }
	    }
	)?
;

dims returns [int dimension = 0] throws SLTranslationException
:
	(LBRACKET RBRACKET { dimension++; } )+
    ;

type returns [KeYJavaType t = null] throws SLTranslationException
:
	(builtintype) => t=builtintype
    |
	t=referencetype
    |
	TYPE
	{
	    raiseNotSupported("\\TYPE");
	}
	
;

referencetype returns [KeYJavaType type = null] throws SLTranslationException
{
    String typename;
}
:
	typename=name
	{
	    try {
		type = resolverManager.resolve(null, typename, null).getKeYJavaType(javaInfo);
	    } catch (NullPointerException e) {
		raiseError("Type " + typename + " not found.");
	    }
	}
;   

builtintype returns [KeYJavaType type = null] throws SLTranslationException
:
	(
	    BYTE 
	    {
		type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_BYTE);
	    }
	|
	    SHORT 
	    {
		type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_SHORT);
	    }
	|
	    INT 
	    {
		type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_INT);
	    }
	|
	    LONG 
	    {
		type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_LONG);
	    }
	|
	    BOOLEAN 
	    {
		type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
	    }
	|
	    VOID 
	    {
		type = null;
	    }
	|
	    BIGINT
	    {
		raiseNotSupported("\\bigint");
	    } 
	|
	    REAL
	    {
		raiseNotSupported("\\real");
	    } 
	)
	
;

name returns [String result = ""] throws SLTranslationException
:
	id:IDENT
	{ result += id.getText(); }
	(
	    DOT id1:IDENT 
	    { result += "." + id1.getText(); }
	)*
;

quantifiedvariabledeclarator[KeYJavaType t] returns [LogicVariable v = null] throws SLTranslationException
{
    int dim = 0;
    KeYJavaType varType = null;
}
:
   id:IDENT (dim=dims)?
   {
	  if (dim > 0) {
	    String fullName;
	    if (t.getJavaType() instanceof ArrayType) {
		fullName = ((ArrayType) t.getJavaType()).getAlternativeNameRepresentation();
	    } else {
		fullName = t.getFullName();
	    }
	    for (int i=0; i < dim; i++) {
		fullName += "[]";
	    }
	    
	    varType = javaInfo.getKeYJavaType(fullName);
	  } else {
		  varType = t;
	  }
	  
	  v = new LogicVariable(new Name(id.getText()), varType.getSort());
   }
;
