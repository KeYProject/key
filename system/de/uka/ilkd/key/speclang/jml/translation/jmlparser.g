//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//Universitaet Koblenz-Landau, Germany
//Chalmers University of Technology, Sweden

//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.



/* -*-antlr-*- */
header {
    package de.uka.ilkd.key.speclang.jml.translation;

    import java.io.StringReader;

    import de.uka.ilkd.key.java.JavaInfo;
    import de.uka.ilkd.key.java.Position;
    import de.uka.ilkd.key.java.Services;
    import de.uka.ilkd.key.java.abstraction.ArrayType;
    import de.uka.ilkd.key.java.abstraction.IteratorOfKeYJavaType;
    import de.uka.ilkd.key.java.abstraction.KeYJavaType;
    import de.uka.ilkd.key.java.abstraction.ListOfKeYJavaType;
    import de.uka.ilkd.key.java.abstraction.PrimitiveType;
    import de.uka.ilkd.key.java.abstraction.SLListOfKeYJavaType;
    import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
    import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
    import de.uka.ilkd.key.logic.BasicLocationDescriptor;
    import de.uka.ilkd.key.logic.EverythingLocationDescriptor;
    import de.uka.ilkd.key.logic.IteratorOfTerm;
    import de.uka.ilkd.key.logic.ListOfTerm;
    import de.uka.ilkd.key.logic.LocationDescriptor;
    import de.uka.ilkd.key.logic.Name;
    import de.uka.ilkd.key.logic.SetAsListOfLocationDescriptor;
    import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
    import de.uka.ilkd.key.logic.SLListOfTerm;
    import de.uka.ilkd.key.logic.Term;
    import de.uka.ilkd.key.logic.TermBuilder;
    import de.uka.ilkd.key.logic.TermCreationException;
    import de.uka.ilkd.key.logic.ldt.LDT;
    import de.uka.ilkd.key.logic.ldt.AbstractIntegerLDT;
    import de.uka.ilkd.key.logic.op.ExactInstanceSymbol;
    import de.uka.ilkd.key.logic.op.Function;
    import de.uka.ilkd.key.logic.op.InstanceofSymbol;
    import de.uka.ilkd.key.logic.op.IteratorOfLogicVariable;
    import de.uka.ilkd.key.logic.op.IteratorOfParsableVariable;
    import de.uka.ilkd.key.logic.op.ListOfLogicVariable;
    import de.uka.ilkd.key.logic.op.ListOfParsableVariable;
    import de.uka.ilkd.key.logic.op.LogicVariable;
    import de.uka.ilkd.key.logic.op.NonRigid;
    import de.uka.ilkd.key.logic.op.Operator;
    import de.uka.ilkd.key.logic.op.ParsableVariable;
    import de.uka.ilkd.key.logic.op.ProgramVariable;
    import de.uka.ilkd.key.logic.op.RigidFunction;
    import de.uka.ilkd.key.logic.op.SLListOfLogicVariable;
    import de.uka.ilkd.key.logic.sort.AbstractSort;
    import de.uka.ilkd.key.logic.sort.ArraySort;
    import de.uka.ilkd.key.logic.sort.ObjectSort;
    import de.uka.ilkd.key.logic.sort.Sort;
    import de.uka.ilkd.key.logic.sort.SortDefiningSymbols;
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
    private static final TermBuilder tb = TermBuilder.DF;
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
	this.excVar	     = exc;
	this.atPreFunctions = atPreFunctions;

	// initialize helper objects
	this.resolverManager = new JMLResolverManager(this.javaInfo,
						      specInClass,
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

	this.intHelper = new JavaIntegerSemanticsHelper(services);

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
	throw excManager.createException("JML feature not supported: " 
			 + feature);
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
	Term result = tb.ff();

	IteratorOfKeYJavaType it = signalsonly.iterator();
	while (it.hasNext()) {
	    KeYJavaType kjt = it.next();
	    SortDefiningSymbols os = (SortDefiningSymbols)(kjt.getSort());
		Function instance
			= (InstanceofSymbol) os.lookupSymbol(InstanceofSymbol.NAME);
	    result = tb.or( result,
		tb.equals(
		    tb.func(instance, tb.var(this.excVar)),
		    trueLitTerm));
	}

	return new FormulaWithAxioms(result);
    }


    public SetOfLocationDescriptor parseAssignable() throws SLTranslationException {

	SetOfLocationDescriptor assignableClause = SetAsListOfLocationDescriptor.EMPTY_SET;

	this.currentlyParsing = true;
	try {
	    assignableClause = assignableclause();
	} catch (antlr.ANTLRException e) {
	    throw excManager.convertException(e);
	}
	this.currentlyParsing = false;

	return assignableClause;
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
	if(term.op() instanceof NonRigid && term.op() != selfVar) {
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
	
	Term[] subTerms = getSubTerms(term);
	Term[] newSubTerms = new Term[subTerms.length];
	for(int i = 0; i < subTerms.length; i++) {
	    newSubTerms[i] = convertToOld(subTerms[i]);
	}
	
	Term result = tb.tf().createTerm(newOp, 
					 newSubTerms, 
					 term.varsBoundHere(0), 
					 term.javaBlock());
	return result;    
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
	
	if (receiver != null) {
	    raiseError("Identifier " + lookupName + " not found!", t);
	}
	
	return null;
    }


    // If a is a boolean literal, the method returns the literal as a Formula.
    private static Term convertToFormula(Term a) {

	if(a.sort() == boolSort) {
	    return tb.equals(a,trueLitTerm);
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
	    
	    SortDefiningSymbols os = (SortDefiningSymbols)(typeExpr.getType().getSort());
	    Function ioFunc = (Function) os.lookupSymbol(ExactInstanceSymbol.NAME);
	     
	    return tb.equals(
		tb.func(ioFunc, typeofExpr.getTypeofTerm()),
		trueLitTerm);
	}
	
	return null;
    }
    
    
    private Term buildEqualityTerm(Term a, Term b) throws SLTranslationException {

	Term result = null;

	try {
	    if(a.sort() != Sort.FORMULA && b.sort() != Sort.FORMULA) {
		result = tb.equals(a,b);
	    } else {
		result = tb.equiv(convertToFormula(a), convertToFormula(b));
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


    /**
     * @param maxmin <code>true</code> for max-Axiom, <code>false</code> for min-Axiom
     *
     * See minor thesis "A translation from JML to Java DL" by Christian Engel, p. 40
     */
    private Term buildMaxMinAxiom(boolean maxmin, Function y, ListOfLogicVariable qVars, Term pred, Term body) {

	Term result = tb.not(tb.ex(qVars.toArray(), pred));

	ProgramVariable n;
	String progVarName;
	String className;
	if (maxmin) {
	    progVarName = "MIN_VALUE";
	} else {
	    progVarName = "MAX_VALUE";
	}

//	System.out.println();
//	System.out.println(qVars.head().sort().toString());
//	System.out.println();

	if (qVars.head().sort().toString().equals("jlong")) {
	    className = "java.lang.Long";
	} else {
	    className = "java.lang.Integer";
	}

	n = javaInfo.getAttribute(progVarName, className);

	result = tb.and(result,
	    tb.equals(
		tb.func(y),
		tb.var(n)));

	Term t = tb.func(y);

	if (maxmin) {
	    t = tb.geq(t,body, services);
	} else {
	    t = tb.leq(t,body, services);
	}

	t = tb.all(qVars.toArray(), tb.imp(pred,t));
	t = tb.and(
	    t,
	    tb.ex(qVars.toArray(),
		tb.and(
		    pred,
		    tb.equals(
			body,
			tb.func(y)))));

	result = tb.or(result, t);

	return result;
    }
    
    
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
	Term lvTerm = tb.var(lv);
	Function repos
		= (Function) ((SortDefiningSymbols) kjt.getSort())
		             .lookupSymbol(AbstractSort.OBJECT_REPOSITORY_NAME);
	Term objectTerm = tb.func(repos, lvTerm); 
	Term guardFma = tb.leq(tb.dot(null, nextToCreate), lvTerm, services); 
	
	//<nextToCreate>
	Term nextToCreateTerm = tb.dot(null, nextToCreate);
	BasicLocationDescriptor nextToCreateLd
		= new BasicLocationDescriptor(nextToCreateTerm);
	result = result.add(nextToCreateLd);
	
	//<created>
	Term createdTerm = tb.dot(objectTerm, createdAttribute);
	BasicLocationDescriptor createdLd 
		= new BasicLocationDescriptor(guardFma, createdTerm);
	result = result.add(createdLd);
		
	//<initialized>
	Term initializedTerm = tb.dot(objectTerm, initializedAttribute);
	BasicLocationDescriptor initializedLd
		= new BasicLocationDescriptor(guardFma, initializedTerm);
	result = result.add(initializedLd); 
	
	//<transient>
	Term transientTerm   = tb.dot(objectTerm, transientAttribute);
	BasicLocationDescriptor transientLd
		= new BasicLocationDescriptor(guardFma, transientTerm);
	result = result.add(transientLd);
	
	//objectTimesFinalized 
	Term objectTimesFinalizedTerm 
			     = tb.dot(objectTerm, objectTimesFinalizedAttribute);
	BasicLocationDescriptor objectTimesFinalizedLd
		= new BasicLocationDescriptor(guardFma, objectTimesFinalizedTerm);
	result = result.add(objectTimesFinalizedLd); 
                                           
    	return result;
    }    
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
    

assignableclause returns [SetOfLocationDescriptor result=SetAsListOfLocationDescriptor.EMPTY_SET] throws SLTranslationException
:
    result=storereflist
    ;
    

storereflist returns [SetOfLocationDescriptor result=SetAsListOfLocationDescriptor.EMPTY_SET] throws SLTranslationException
{
    SetOfLocationDescriptor mod = null;
}
:
    mod=storeref { result = result.union(mod); } 
	("," mod=storeref { result = result.union(mod); } )*
    ;


storeref returns [SetOfLocationDescriptor result = SetAsListOfLocationDescriptor.EMPTY_SET] throws SLTranslationException
:
	result=storerefexpression
    |   LPAREN MULT { raiseError("informal descriptions not supported (for obvious reason)"); } //TODO: should be a warning!
    |   result=storerefkeyword
    ;

storerefexpression returns [SetOfLocationDescriptor result = SetAsListOfLocationDescriptor.EMPTY_SET] throws SLTranslationException
{
    JMLExpression expr;
    BasicLocationDescriptor ld = null;
}
:
    expr=storerefname 
    (
	ld=storerefnamesuffix[expr]   { expr = new JMLExpression(ld.getLocTerm()); }
    )*
    {
	if(ld == null) {
	    try {
		ld = new BasicLocationDescriptor(expr.getTerm());
	    } catch(IllegalArgumentException e) {
		raiseError(e.getMessage());
	    }
	}
	result = result.add(ld);
    }
    ;


storerefname returns [JMLExpression result = null] throws SLTranslationException
:
    id:IDENT
    {
	result = lookupIdentifier(id.getText(), null, null, id);
	if(result == null) {
	    raiseError("identifier not found: " + id.getText());
	}
    }
    | "super"
    {
	raiseNotSupported("location \"super\"");
    }
    | "this"
    {
	result = new JMLExpression(tb.var(selfVar));
    }
    ;
    

storerefnamesuffix[JMLExpression receiver] returns [BasicLocationDescriptor ld=null] throws SLTranslationException
{
    Term refTerm=null;
}
:
    DOT id:IDENT
    {
	JMLExpression expr = lookupIdentifier(id.getText(), receiver, null, id);
	if (!expr.isTerm()) {
	    raiseError("Error in store-ref-suffix");
	}
	try {
	    ld = new BasicLocationDescriptor(expr.getTerm());
	} catch (IllegalArgumentException e) {
	    raiseError(e.getMessage());
	}
    }
    | DOT "this"
    {
	raiseNotSupported("location \"this\" as store-ref-suffix");
    }
    | "[" ld=specarrayrefexpr[receiver] "]"
    | DOT MULT
    {
	raiseNotSupported("location \"*\" as store-ref-suffix");
    }
    ;

specarrayrefexpr[JMLExpression receiver] returns [BasicLocationDescriptor result=null] throws SLTranslationException
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
	Term indexTerm;
	Term guardTerm;

	   if (rangeFrom == null) {
	    // We have a star. A star includes all components of an array even
	    // those out of bound. This makes proving easier.	    
	    LogicVariable indexVar = new LogicVariable(new Name("i"), 
			     services.getTypeConverter().getIntegerLDT().targetSort());
	    indexTerm = tb.var(indexVar);	
	    guardTerm = tb.tt();	    
	} else if (rangeTo != null) {
	    LogicVariable indexVar = new LogicVariable(new Name("i"), 
			     services.getTypeConverter().getIntegerLDT().targetSort());
	    indexTerm = tb.var(indexVar);
	    guardTerm = tb.and(
		tb.leq(rangeFrom, indexTerm, services),
		tb.leq(indexTerm, rangeTo, services)
		);
	} else {
	    indexTerm = rangeFrom;
	    guardTerm = tb.tt();
	}
 
	try {
	    Term resTerm = tb.array(receiver.getTerm(), indexTerm);
	    result = new BasicLocationDescriptor(guardTerm, resTerm);
	} catch (TermCreationException e) {
	    raiseError(e.getMessage());
	} catch (IllegalArgumentException e) {
	    raiseError(e.getMessage());
	}
    }
    ;

storerefkeyword returns [SetOfLocationDescriptor result = SetAsListOfLocationDescriptor.EMPTY_SET] throws SLTranslationException
{
    KeYJavaType t = null;
}
:
    NOTHING
    | EVERYTHING { result = EverythingLocationDescriptor.INSTANCE_AS_SET; }
    | NOT_SPECIFIED { result = EverythingLocationDescriptor.INSTANCE_AS_SET; }
    | OBJECT_CREATION LPAREN t=referencetype RPAREN  { result = getObjectCreationModSet(t); }
;


signalsonlyclause returns [ListOfKeYJavaType result = SLListOfKeYJavaType.EMPTY_LIST] throws SLTranslationException
{
    KeYJavaType t=null;
}
:
	NOTHING
    |   t=referencetype { result = result.append(t); } ("," t=referencetype { result = result.append(t); })*
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
		result = tb.tt();
	    } else {
		Map /* Operator -> Operator */ replaceMap = new LinkedHashMap();
		replaceMap.put(eVar, excVar);
		OpReplacer excVarReplacer = new OpReplacer(replaceMap);
		
		SortDefiningSymbols os = (SortDefiningSymbols)(excType.getSort());
		Function instance
		    = (InstanceofSymbol) os.lookupSymbol(InstanceofSymbol.NAME);
		
		result = tb.imp(
		    tb.equals(tb.func(instance, tb.var(excVar)), trueLitTerm),
		    convertToFormula(excVarReplacer.replace(result)));
	    }
	}
    ;

predornot returns [Term result=null] throws SLTranslationException
:
	result=predicate
    |   "\\not_specified"
    |   "\\same"
    ;
    
predicate returns [Term result=null] throws SLTranslationException
:
	result=specexpression
    ;

specexpression returns [Term result=null] throws SLTranslationException
:
	result=expression
    ;

spec_expression_list throws SLTranslationException
{
    Term t;
}
:
	t=specexpression ("," t=specexpression)*
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


/* not used JML expressions
assignmentOp
:
	"=" 
    |   "+="
    |   "-="
    |   "*="
    |   "/="
    |   "%="
    |   ">>="  
    |   ">>>="
    |   "<<="
    |   "&="
    |   "|="
    |   "^="
    ;
*/	
conditionalexpr returns [Term result=null] throws SLTranslationException
{
    Term a,b;
}
:
	result=equivalenceexpr 
	(
	    "?" a=conditionalexpr ":" b=conditionalexpr
	    {
		result = tb.ife(convertToFormula(result),a,b);
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
		result = tb.not(t);
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
	    "==>" t=impliesnonbackwardexpr
	    {
		result = tb.imp(convertToFormula(result),convertToFormula(t));
	    }
	    
	  |
	    (
		"<==" t=logicalorexpr
		{
		    result = tb.imp(convertToFormula(t),convertToFormula(result));
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
	    "==>" t=impliesnonbackwardexpr
	    {
		result = tb.imp(convertToFormula(result),convertToFormula(t));
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
	    "||" t=logicalorexpr
	    {
		result = intHelper.buildOrExpression(t,result);
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
	    "&&" t=logicalandexpr
	    {
		result = intHelper.buildAndExpression(t,result);
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
	    "|" t=inclusiveorexpr
	    {
	       result = intHelper.buildPromotedOrExpression(result,t);
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
	    result = intHelper.buildPromotedXorExpression(result,t);
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
	    "&" t=andexpr
	    { 
		result = intHelper.buildPromotedAndExpression(result,t);
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
	    eq:"==" right=equalityexpr
	    {
		if (result.isType() ^ right.isType()) {
		    raiseError("Cannot build equality expression between term " +
			"and type.", eq);
		}
		result = new JMLExpression(buildEqualityTerm(result, right));
	    }
	|
	    ne:"!=" right=equalityexpr
	    {
		if (result.isType() ^ right.isType()) {
		    raiseError("Cannot build equality expression between term " +
			"and type.", ne);
		}
		result = new JMLExpression(tb.not(buildEqualityTerm(result, right)));
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
		SortDefiningSymbols os = (SortDefiningSymbols)(type.getSort());
		f = (InstanceofSymbol) os.lookupSymbol(InstanceofSymbol.NAME);
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
		
		SortDefiningSymbols os = (SortDefiningSymbols)(right.getType().getSort());
		Function ioFunc = (InstanceofSymbol) os.lookupSymbol(InstanceofSymbol.NAME);
		
		result = new JMLExpression(
		    tb.equals(
			tb.func(ioFunc, result.getTypeofTerm()),
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
				tb.func(f, result.getTerm()));
			} else {
			    if (right.isType()) {
			    raiseError("Cannot build relational expression from type " +
				right.getType().getName() + ".", opToken);
			    }
			    assert right.isTerm();
			    
			    result = new JMLExpression(
				tb.func(f,result.getTerm(),right.getTerm()));
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
	">>" e=additiveexpr
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
	"<<" e=additiveexpr 
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
	">>>" e=additiveexpr 
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
	"+" e=multexpr
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
	"-" e=multexpr
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
	"%" e=unaryexpr
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
       "+" result=unaryexpr
	{
	    if (result.isType()) {
		raiseError("Cannot build  +" + result.getType().getName() + ".");
	    }
	    assert result.isTerm();
	    
	    result = new JMLExpression(
		intHelper.buildPromotedUnaryPlusExpression(result.getTerm()));
	}
    |
	"-" result=unaryexpr
	{
	    if (result.isType()) {
		raiseError("Cannot build  -" + result.getType().getName() + ".");
	    }
	    assert result.isTerm();

	    result = new JMLExpression(
		intHelper.buildUnaryMinusExpression(result.getTerm()));
	}
    |
	("(" typespec ")" ) => 
	   "(" type=typespec ")" result=unaryexpr
	
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
		    resultTerm = tb.func(castFunction, resultTerm);
		 } 
		 
		 castFunction = ((AbstractSort) type.getSort()).getCastSymbol();
		 
		 
		 result = new JMLExpression(
		     tb.func(castFunction, resultTerm));
	     }
	}
;


unaryexprnotplusminus returns [JMLExpression result=null] throws SLTranslationException
{
    JMLExpression e;
}
:
	"!" e=unaryexpr
	{
	    if (e.isType()) {
		raiseError("Cannot negate type " + e.getType().getName() + ".");
	    }
	    
	    Term t = e.getTerm();
	    assert t != null;
	    
	    if (t.sort() == Sort.FORMULA) {
		result = new JMLExpression(tb.not(t));
	    } else if (t.sort() == boolSort) {
		result = new JMLExpression(tb.not(tb.equals(t,trueLitTerm)));
	    } else {
		raiseError("Wrong type in not-expression: " + t);
	    }
	}
    |   
	"~" e=unaryexpr
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
	    expr=primarysuffix[expr, fullyQualifiedName]
	    {
		fullyQualifiedName += "." + LT(0).getText();
	    }
	)*
	
	{
	    if (expr == null) {
		raiseError("Expression " + fullyQualifiedName + " not found!");
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
    |   "true"       { result = new JMLExpression(tb.tt()); }
    |   "false"      { result = new JMLExpression(tb.ff()); }
    |   "null"       { result = new JMLExpression(tb.NULL(services)); }
    |   result=jmlprimary 
    |   "this"       { result = new JMLExpression(tb.var(selfVar)); }
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
	    result = lookupIdentifier(lookupName, receiver, null, id);
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
	lbrack:"[" t=expression "]"
	{
	    if (receiver == null) {
		raiseError("Array \"" + fullyQualifiedName + "\" not found.", lbrack);
	    }
	    if (receiver.isType()) {
		raiseError("Error in array expression: \"" + fullyQualifiedName +
		    "\" is a type.", lbrack);
	    }
	    
	    try {
		    result = new JMLExpression(tb.array(receiver.getTerm(),t));
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
	"new" typ=type new_suffix
	
    ;

new_suffix throws SLTranslationException
{
    ListOfTerm terms;
}
:
	"(" ( terms=expressionlist )? ")" 
    ;

expressionlist returns [ListOfTerm result=SLListOfTerm.EMPTY_LIST] throws SLTranslationException
{ 
    Term t;
}
:
	t=expression { result = result.append(t); } ("," t=expression {result = result.append(t);} )* 
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
	Term intTerm = tb.zTerm(services,decInteger.toString());
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
	Term intTerm = tb.zTerm(services,n.getText());
	result = intHelper.castToLDTSort(intTerm, 
					 services.getTypeConverter()
					     	 .getIntLDT());
    }
;

jmlprimary returns [JMLExpression result=null] throws SLTranslationException
{
    Term t;
    KeYJavaType typ;
}
:
	RESULT
	{
	    if (resultVar==null) {
		raiseError("\\result used in wrong context");
	    }
	    result = new JMLExpression(tb.var(resultVar));
	}
    |
	("(" QUANTIFIER) => t=specquantifiedexpression
	{
	    result = new JMLExpression(t);
	}
    |
	(OLD | PRE) "(" t=specexpression ")"
	{
	    if (atPreFunctions == null) {
		raiseError("JML construct " +
			   "\\old not allowed in this context.");
	    }
	    
	    result = new JMLExpression(convertToOld(t));
	}
    |   
	CREATED "(" t=specexpression ")"
	{
	    if (t.sort() instanceof ObjectSort) {
		result = new JMLExpression(
		    CreatedAttributeTermFactory.INSTANCE.
			createCreatedTerm(services, t));
	    } else {
		raiseError("\\created only allowed for reference types.");
	    }
	}
	
    |
	NONNULLELEMENTS "(" t=specexpression ")"
	{
	    Term resTerm = tb.not(tb.equals(t, tb.NULL(services)));

	    if (t.sort() instanceof ArraySort) {
		LogicVariable i = new LogicVariable(new Name("i"), javaInfo
				.getKeYJavaType(PrimitiveType.JAVA_INT)
				.getSort());

		// See JML reference manual
		// http://www.cs.iastate.edu/~leavens/JML/jmlrefman/jmlrefman_11.html#SEC139		
		Term range = tb.and(
		    tb.leq(tb.zTerm(services, "0"), tb.var(i), services),
		    tb.leq(tb.var(i), tb.dot(t,javaInfo.getArrayLength()), services));
		Term body = tb.equals(
		    tb.array(t, tb.var(i)),
		    tb.NULL(services));
		body = tb.not(body);
		body = tb.imp(range, body);

		result = new JMLExpression(tb.and(resTerm, tb.all(i, body)));
	    }
	}
	
    |   INFORMAL_DESCRIPTION 
	{
	    raiseNotSupported("informal predicates");
	}
//    |   NOT_MODIFIED "(" storereflist ")" 
	
    |   FRESH "(" spec_expression_list ")"
	{
	    raiseNotSupported("\\fresh");
	} 
	
    |   REACH "(" t=specexpression ")"
	{
	    raiseNotSupported("\\reach");
	} 
	
    |   DURATION "(" t=expression ")" 
	{
	    raiseNotSupported("\\duration");
	} 
	
    |   SPACE "(" t=specexpression ")" 
	{
	    raiseNotSupported("\\space");
	} 
	
    |   WORKINGSPACE "(" t=expression ")"
	{
	    raiseNotSupported("\\working_space");
	} 
	
    |   TYPEOF "(" t=specexpression ")"
	{
	    result = new JMLExpression(services.getTypeConverter().getKeYJavaType(t),t);
	} 
	
    |   ELEMTYPE "(" t=specexpression ")" 
	{
	    raiseNotSupported("\\elemtype");
	} 
	
    |   TYPE_SMALL "(" typ=typespec ")" 
	{
	    result = new JMLExpression(typ);
	} 
	
    |   LOCKSET
	{
	    raiseNotSupported("\\lockset");
	} 
	
    |   IS_INITIALIZED "(" typ=referencetype ")" 
	{
	    Term resTerm = tb.equals(
		tb.var(
		    javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED, 
					  typ)),
		tb.TRUE(services));
	    result = new JMLExpression(resTerm);
	} 
	
    |   INVARIANT_FOR "(" t=specexpression ")" 
	{
	    raiseNotSupported("\\invariant_for");
	} 
	
    |   ( "(" LBLNEG ) => "(" LBLNEG IDENT t=specexpression ")"
	{
	    result = new JMLExpression(t);
//	    raiseNotSupported("\\lblneg");
	} 
	
    |   ( "(" LBLPOS ) => "(" LBLPOS IDENT t=specexpression ")" 
	{
	    result = new JMLExpression(t);
//	    raiseNotSupported("\\lblpos");
	} 
	
    |
	NOWARN 
	{
	    raiseNotSupported("\\nowarn");
	} 

    |   
	"(" t=expression ")"
	{
	    result = new JMLExpression(t);
	}
;

specquantifiedexpression returns [Term result = null] throws SLTranslationException
{
    Term t = null;
    Term p = tb.tt();
    boolean nullable = false;
    ListOfLogicVariable declVars = null;
}
:
	"("
	q:QUANTIFIER (nullable=boundvarmodifiers)? declVars=quantifiedvardecls ";"
	
	{
	    resolverManager.pushLocalVariablesNamespace();
	    resolverManager.putIntoTopLocalVariablesNamespace(declVars);
	} 
	(
	    ((predicate)? ";" ) => (p=predicate)? ";" t=specexpression
	|
	    (";")? t=specexpression 
	)
	
	{
	    resolverManager.popLocalVariablesNamespace();
	    
	    //add implicit "non-null" guards for reference types, 
	    //"in-bounds" guards for integer types
	    Term nullTerm = tb.NULL(services);
	    for(IteratorOfLogicVariable it = declVars.iterator(); 
	        it.hasNext(); ) {
	        LogicVariable lv = it.next();
	        
	    	if(lv.sort() instanceof ObjectSort && !nullable) {
		    p = tb.and(p, tb.not(tb.equals(tb.var(lv), nullTerm)));
		} else {
	    	    LDT ldt 
	    	    	= services.getTypeConverter().getModelFor(lv.sort());
		    if(ldt instanceof AbstractIntegerLDT) {
	    		Function inBounds 
	    			= ((AbstractIntegerLDT) ldt).getInBounds();
	    	    	p = tb.and(p, tb.func(inBounds, tb.var(lv)));
	    	    }
	    	}
	    }	    
	    
	    t = convertToFormula(t);
	    
	    if (q.getText().equals("\\forall")) {
		if (p != null) {
		    t = tb.imp(p, t);
		}
		result = tb.all(declVars.toArray(), t);
	    }
	    else if (q.getText().equals("\\exists")) {
		if (p != null) {
		    t = tb.and(p, t);
		}
		result = tb.ex(declVars.toArray(), t);
	    }
	    else if (q.getText().equals("\\min")) {
		Function y = new RigidFunction(
		    new Name("_jml_ymin"+(varCounter++)),
		    declVars.head().sort(),
		    new Sort[] {});
		axiomCollector.collectAxiom(y,
		    buildMaxMinAxiom(false, y, declVars, p, t));
		result = tb.func(y);
		services.getNamespaces().functions().addSafely(y);
	    }
	    else if (q.getText().equals("\\max")) {
		Function y = new RigidFunction(
		    new Name("_jml_ymax"+(varCounter++)),
		    declVars.head().sort(),
		    new Sort[] {});
		axiomCollector.collectAxiom(y,
		    buildMaxMinAxiom(true, y, declVars, p, t));
		result = tb.func(y);
		services.getNamespaces().functions().addSafely(y);
	    }
	    else if (q.getText().equals("\\num_of")) {
		raiseNotSupported("\\num_of");
	    }
	    else if (q.getText().equals("\\product")) {
		raiseNotSupported("\\product");
	    }
	    else if (q.getText().equals("\\sum")) {
		raiseNotSupported("\\sum");
	    }
	    else {
		raiseError("Unknown quantifier: " + q.getText() + "!");
	    }
	}
	")"
;

quantifiedvardecls returns [ListOfLogicVariable vars = SLListOfLogicVariable.EMPTY_LIST] throws SLTranslationException
{
    KeYJavaType t = null;
    LogicVariable v = null;
}
:
	t=typespec v=quantifiedvariabledeclarator[t] 
	
	{ vars = vars.append(v); }
	
	(
	    "," v=quantifiedvariabledeclarator[t]
	    
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
	("[" "]" { dimension++; } )+
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
	    "byte" 
	    {
		type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_BYTE);
	    }
	|
	    "short" 
	    {
		type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_SHORT);
	    }
	|
	    "int" 
	    {
		type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_INT);
	    }
	|
	    "long" 
	    {
		type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_LONG);
	    }
	|
	    "boolean" 
	    {
		type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
	    }
	|
	    "void" 
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
