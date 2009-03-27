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
    package de.uka.ilkd.key.speclang.ocl.translation;

    import de.uka.ilkd.key.collection.IteratorOfString;
    import de.uka.ilkd.key.collection.ListOfString;
    import de.uka.ilkd.key.collection.SLListOfString;
    import de.uka.ilkd.key.java.abstraction.KeYJavaType;
    import de.uka.ilkd.key.java.abstraction.PrimitiveType;
    import de.uka.ilkd.key.java.declaration.TypeDeclaration;
    import de.uka.ilkd.key.java.JavaInfo;
    import de.uka.ilkd.key.java.Position;
    import de.uka.ilkd.key.java.Services;
    import de.uka.ilkd.key.logic.*;
    import de.uka.ilkd.key.logic.op.*;
    import de.uka.ilkd.key.logic.sort.*;
    import de.uka.ilkd.key.speclang.translation.AxiomCollector;
    import de.uka.ilkd.key.speclang.translation.JavaIntegerSemanticsHelper;
    import de.uka.ilkd.key.speclang.translation.SLTranslationException;
    import de.uka.ilkd.key.speclang.translation.SLTranslationExceptionManager;
    import de.uka.ilkd.key.util.Debug;
    import de.uka.ilkd.key.proof.AtPreFactory;
    
    import java.lang.*;
    import java.lang.AssertionError;
    import java.util.Map;
    import java.util.LinkedHashMap;
}

class KeYOCLParser extends Parser;

options {
	importVocab=KeYOCLLexer;
	k=2;
	defaultErrorHandler=false;
}

{
    //constants
    private static final FunctionFactory funcFactory = FunctionFactory.INSTANCE;
    private static final TermBuilder tb = TermBuilder.DF;
    private static final AtPreFactory APF = AtPreFactory.INSTANCE;
    
    //parameters
    private Services services;
    private JavaInfo javaInfo;
    private Namespace funcNS;
    private Namespace sortNS;
    private Namespace varNS;
    private Map /*operator (normal) -> function (atPre)*/ atPreFunctions;
    
    //variables for variables
    private ParsableVariable selfVar;
    private ListOfParsableVariable paramVars;
    private ParsableVariable resultVar;
    private ParsableVariable excVar;
        
    //helper objects
    private FormulaBoolConverter formulaBoolConverter;
    private OCLResolverManager OCLResolverManager;
    private AxiomCollector axiomCollector;
    private JavaIntegerSemanticsHelper intHelper;
    private SLTranslationExceptionManager excManager;
    
    private boolean preConditionParser;    

    /**
     * @param lexer the associated lexer
     */
    public KeYOCLParser(TokenStream lexer,
                        Position offsetPos,
                        Services services,
 			            KeYJavaType specInClass,
 			            AxiomCollector ac,
 			            ParsableVariable selfVar,
 			            ListOfParsableVariable paramVars,
 			            ParsableVariable resultVar,
 			            ParsableVariable excVar,
 			            /*inout*/ Map /*operator (normal)
 			            -> function (atPre)*/ atPreFunctions) {
        this(lexer);
        
    	//save parameters        
        this.services = services;
        javaInfo = services.getJavaInfo();
        NamespaceSet nss = services.getNamespaces();
        funcNS   = nss.functions();
        sortNS   = nss.sorts();
        varNS    = nss.variables();
        this.selfVar        = selfVar;
        this.paramVars      = paramVars;
        this.resultVar      = resultVar;
        this.excVar         = excVar;
        this.atPreFunctions = atPreFunctions;
        
        String fileName = "no file";
        if (specInClass.getJavaType() instanceof TypeDeclaration) {
		fileName = ((TypeDeclaration)specInClass.getJavaType())
                                .getPositionInfo().getFileName();
        }
        
        this.excManager = new SLTranslationExceptionManager(this,
                                			    fileName, 
                                	                    offsetPos);
                                
                
        //set axiomCollector
        axiomCollector = ac;
        
        //initialise formula-bool-converter
        formulaBoolConverter = new FormulaBoolConverter(services, nss);
        
        //initialise integer helper
        intHelper = new JavaIntegerSemanticsHelper(services, excManager);
        
        //initialise property manager
        OCLResolverManager = new OCLResolverManager(services,
                                              	    specInClass,
                                              	    selfVar,
                                              	    formulaBoolConverter,
                                              	    excVar,
                                              	    excManager);
        OCLResolverManager.pushLocalVariablesNamespace();
        if(selfVar != null) {
	        OCLResolverManager.putIntoTopLocalVariablesNamespace(selfVar);
        }
        if(paramVars != null) {
			IteratorOfParsableVariable it = paramVars.iterator(); 
			while(it.hasNext()) {
				OCLResolverManager.putIntoTopLocalVariablesNamespace(it.next());
			}
        }
        if(resultVar != null) {
		 	OCLResolverManager.putIntoTopLocalVariablesNamespace(resultVar);
		}
		
		if(excVar == null) {
		    preConditionParser = true;
		} else {
		    preConditionParser = false;
		}
	}
    

    private int getLine() {
        int line = -1;
        try {
            line = LT(0).getLine();
        } catch (TokenStreamException e) {
            System.err.println("No further token in stream");
        }
        return line;
    }   

    private int getColumn() {
        int col = -1;
        try {
            col = LT(0).getColumn();
        } catch (TokenStreamException e) {
            System.err.println("No further token in stream");
        }
        return col;
    }   
    
    
    private void raiseError(antlr.ANTLRException e) throws SLTranslationException {
        throw excManager.convertException(e);
    }
    
    
    private void raiseError(String message) throws SLTranslationException {
        throw excManager.createException("OCL Parser Error: " + message);
    }
       
    
    /**
     * Extracts a term's subterms as an array.
     */
    private Term[] getSubTerms(Term term) {
    	Term[] result = new Term[term.arity()];
    	for(int i = 0; i < term.arity(); i++) {
    		result[i] = term.sub(i);
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
     * Converts a term so that its top-level operator refers to the pre-state.
     * Creates and saves new atPreFunctions when necessary.
     */
    private Term convertToAtPre(Term term) {
        assert atPreFunctions != null;
        
        Operator newOp;
        if(term.op() instanceof NonRigid) {
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
		
	final Term[] subTerms = getSubTerms(term);
	
	for(int i = 0; i < subTerms.length; i++) {
	    vars[i] = term.varsBoundHere(i);
	}
        
        Term result = tb.tf().createTerm(newOp, 
                                         subTerms, 
                                         vars, 
                                         term.javaBlock());
        return result;
    }
    
    
    /**
     * Builds a term representing equality among two OCLEntities
     * depending on their type. If the types are not compatible,
     * null is returned.
     */
    private Term buildEqualityTermByEntity(OCLExpression a, OCLExpression b)
    {
    	Term result = null;
        Sort boolSort = services.getJavaInfo()
                                .getKeYJavaType(PrimitiveType.JAVA_BOOLEAN)
                                .getSort();
		
		if(a.isTerm() && b.isTerm()) {
			if ((a.getTerm().sort() == Sort.FORMULA) &&
			    (b.getTerm().sort() == Sort.FORMULA)) {
			    result = tb.equiv(a.getTerm(),b.getTerm());
			} else {
			    result = tb.equals(
			        formulaBoolConverter.convertFormulaToBool(a.getTerm()),
			        formulaBoolConverter.convertFormulaToBool(b.getTerm()));
			}
		}
		if(a.isCollection() && b.isCollection()) {
			Sort csort = ((OCLCollection) a.getCollection()).getFunctionalRestriction().sort();
			LogicVariable v = new LogicVariable(
			    //TODO: change variable-name
			    new Name("e"),
                ((AbstractCollectionSort) csort).elementSort());
			if(((OCLCollection) a.getCollection()).isSet() && ((OCLCollection) b.getCollection()).isSet()) {
				Function isIn = (Function) funcNS.lookup(new Name(csort.name().toString()+"::includes"));
				Term subTerm = tb.equiv(
				    tb.func(isIn,
				        ((OCLCollection) a.getCollection()).getFunctionalRestriction(),
				        tb.var(v)),
				    tb.func(isIn,
				        ((OCLCollection) b.getCollection()).getFunctionalRestriction(),
				        tb.var(v)));
				result = tb.all(v,subTerm);
			}
			if(((OCLCollection) a.getCollection()).isBag() && ((OCLCollection) b.getCollection()).isBag()) {
				Function count = (Function) funcNS.lookup(new Name(csort.name().toString()+"::count"));
				Term subTerm = tb.equiv(
				    tb.func(count,
				        ((OCLCollection) a.getCollection()).getFunctionalRestriction(),
				        tb.var(v)),
				    tb.func(count,
				        ((OCLCollection) b.getCollection()).getFunctionalRestriction(),
				        tb.var(v)));
				result = tb.all(v,subTerm);
			}
		}
		return result;
    }
    
        
    /**
     * Initialises the parser's counters.
     * @param initialValues the inital values to use, or an empty list to use 
     * default values
     */
    public void setCounters(ListOfInteger initialValues) {
    	IteratorOfInteger it = initialValues.iterator();
    	if(it.hasNext()) {
    		formulaBoolConverter.setVariableCounter(it.next().intValue());
    	}
    }
    
    
    /**
     * Returns the values of the parser's counters, to be used as 
     * initial values for some other parser instance.
     */
    public ListOfInteger getCounters() {
    	int boolCounter = formulaBoolConverter.getVariableCounter();
    	return SLListOfInteger.EMPTY_LIST.append(new Integer(boolCounter));
    }
    
    
    /**
     * Parses the expression passed to the constructor.
     */
    public Term parseExpression() throws SLTranslationException {
        
    	OCLExpression expr = null;
    	try {
            expr = expression();
		} catch (antlr.ANTLRException e) {
			raiseError(e);
		}
    	        
        if(expr == null) {
            raiseError("Fatal OCL-Translation error.");
        }
        
        Term result = expr.getTerm();
        
        if (result == null) {
            raiseError("Unknown OCL-Translation error.");
        }
        
        result = formulaBoolConverter.addAxioms(result);
    	
    	// this should be done by the AxiomCollector/POs
    	//result = funcFactor.addAxioms(result);
    	
    	// Add created functions to the namespace
    	funcNS.add(funcFactory.getFunctions());
    	IteratorOfLogicVariable it = funcFactory.getCreatedVars().iterator();
    	while(it.hasNext()) {
    		// HACK - has to be fixed!
    		Named next = it.next();
    		if(varNS.lookup(new Name(next.name().toString()))==null) {
    			varNS.addSafely(next);	
    		}
    	}
        return result;
    }    
}



//-----------------------------------------------------------------------------
//Rules which are not currently used, since we only parse at expression level
//-----------------------------------------------------------------------------

top throws SLTranslationException
{
	OCLExpression t;
}
	: 
		t = oclExpression 
	    { 
    		Debug.fail("Should be never entered. Only workaround of an antlr bug."); 
	    }
	;


oclFile throws SLTranslationException
	: 	( "package" packageName oclExpressions "endpackage" )+
	;


packageName throws SLTranslationException
{
	String s;
}
	: 	s=pathName
	;


oclExpressions throws SLTranslationException
	:	(constraint)*
	;


constraint throws SLTranslationException
{
	OCLExpression t;
}
	: 
		contextDeclaration 
	    (   
	    	("def" (NAME)? COLON (letExpression)*)
    	    | 
    	    (stereotype (NAME)? COLON t=oclExpression)
	    )+
	;


contextDeclaration throws SLTranslationException
	: 
		"context" (operationContext | classifierContext)
	;


classifierContext throws SLTranslationException
	: 	(NAME COLON NAME)
	| 	NAME
	;


operationContext throws SLTranslationException
	: 
		NAME DCOLON operationName LPAREN formalParameterList RPAREN
	    ( COLON returnType )?
	;


returnType throws SLTranslationException
  	: 	typeSpecifier
  	;


stereotype throws SLTranslationException
    :	"pre"
	| 	"post"
    | 	"inv"
    ;


operationName throws SLTranslationException
  	:	NAME 
    |	EQUAL
    |	PLUS
    |	MINUS
    |	LT
    |	LE
    |	GE
    |	GT
    |	DIVIDE
    | 	MULT
    | 	NEQUAL
    | 	IMPLIES
    | 	NOT
    | 	OR
    | 	XOR
    | 	AND
    |   MODULO
    ;


oclExpression returns [OCLExpression result=null] throws SLTranslationException
  	:	( (letExpression)* "in" )?  result=expression
  	;
  	

letExpression throws SLTranslationException
{
	OCLExpression t;
}
  	: 
  		"let" NAME 
  		//( LPAREN formalParameterList RPAREN )?         // not allowed anymore in OCL2.0
    	( COLON typeSpecifier )?
    	EQUAL t=expression
  	;
  	
  	
formalParameterList throws SLTranslationException
  	: 
  		( 
  			NAME COLON typeSpecifier 
      		(COMMA NAME COLON typeSpecifier)*
    	)?
  	;  	




//-----------------------------------------------------------------------------
//Rules for expressions and below
//-----------------------------------------------------------------------------

expression returns [OCLExpression result=null] throws SLTranslationException
  	: result=implicationExpression
  	;


implicationExpression returns [OCLExpression result=null] throws SLTranslationException
{
	OCLExpression a=null;
}
  	: 
  		result=logicalExpression
        ( 
           	IMPLIES a=logicalExpression
            {
                result = new OCLExpression(
                    tb.imp(result.getTerm(),a.getTerm()));
            }
        )* 
	;


logicalExpression returns [OCLExpression result=null] throws SLTranslationException
{
	OCLExpression a=null;
	Junctor j=null;
}
  	: 
  		result=relationalExpression
        ( 
            (XOR relationalExpression) => XOR a=relationalExpression
            {
                result = new OCLExpression(
                    tb.not(
                        tb.equals(
                            result.getTerm(),
                            a.getTerm())));
            }
            |
           	j=logicalOperator a=relationalExpression
            {
                result = new OCLExpression(
                    tb.tf().createJunctorTermAndSimplify(
                        j,
                        result.getTerm(),
                        a.getTerm()));
            }
        )* 
	;


relationalExpression returns [OCLExpression result=null] throws SLTranslationException
{
	OCLExpression a=null;
	Function f=null;
}
	: 
		result=additiveExpression
	    ( 
            (EQUAL additiveExpression) => EQUAL a=additiveExpression 
	        {
    			result = new OCLExpression(
    			    buildEqualityTermByEntity(result,a));
	        }
            | 
            (NEQUAL additiveExpression) => NEQUAL a=additiveExpression
            {
    			result = new OCLExpression(
    			    tb.not(
    			        buildEqualityTermByEntity(result,a)));

    	    }  
            | 
            f=relationalOperator a=additiveExpression 
            {
            	result = new OCLExpression(
            	    tb.func(
            	        (Function) f,
            	        result.getTerm(),
            	        a.getTerm()));
            }
		)?
		{
			//Debug.assertTrue(result.isTerm());
			//Debug.assertTrue(result.getTerm()!=null);
		}
	;


additiveExpression returns [OCLExpression result=null] throws SLTranslationException
{
	OCLExpression a=null;
	Operator op=null; 
}
  	: 
  		result=multiplicativeExpression
	    (
	        PLUS a=multiplicativeExpression
	        {
           		if (!result.isTerm() | !a.isTerm()) {
	       			raiseError("Wrong expression in additive expression. One of the summands is not a term.");
	       		}
	        		
       	        result = new OCLExpression(
       	                intHelper.buildAddExpression(result.getTerm(),a.getTerm()));
	        }

	        |

	        MINUS a=multiplicativeExpression
	        {
        		if (!result.isTerm() | !a.isTerm()) {
        			raiseError("Wrong expression in subtractive expression. One of the summands is not a term.");
        		}
	        		
       	        result = new OCLExpression(
       	                intHelper.buildSubExpression(result.getTerm(),a.getTerm()));
	        }
    	)*
	;


multiplicativeExpression returns [OCLExpression result=null] throws SLTranslationException
{
	OCLExpression a=null;
    Operator op=null; 
}
  	: 
  		result=unaryExpression
	    ( 
	        MULT a=unaryExpression
	        {
        		if (!result.isTerm() | !a.isTerm()) {
        			raiseError("Wrong expression in multiplicative expression. One of the factors is not a term.");
        		}
        		
       	        result = new OCLExpression(
       	                intHelper.buildMulExpression(result.getTerm(),a.getTerm()));
	        }
	        
	        |
	        
	        DIVIDE a=unaryExpression
	        {
       	        raiseError("division '/' not supported (no reals supported).");
	        }
	    )*
  	;


unaryExpression returns [OCLExpression result=null] throws SLTranslationException
	: 
		(NOT postfixExpression) => NOT result=postfixExpression
	    {
    		result = new OCLExpression(
    		    tb.not(result.getTerm()));
	    }
		| 
		(MINUS postfixExpression) => MINUS result=postfixExpression
    	{
    		Function neg = (Function) funcNS.lookup(new Name("neg"));
    		result = new OCLExpression(
    		    tb.func(neg,result.getTerm()));
    	}
  		| 
  		result=postfixExpression
  	;


postfixExpression returns [OCLExpression result=null] throws SLTranslationException
{
	OCLExpression entity=null;
}
  	: 
		entity=primaryExpression
	    (
	    	(DOT | (RARROW {entity = entity.isTerm() ? entity.asCollection() : entity;})) 
	    	  entity=propertyCall[entity]
	    )*
	    {
	    	result = entity;
	    	if (result == null) {
	    	    raiseError("Error in postfix expression.");
	    	}
	    }
	;
  
  
primaryExpression returns [OCLExpression result=null] throws SLTranslationException
{
	Term t;
	OCLCollection c;
}
  	:   c=literalCollection { result = new OCLExpression(c); }
  	| 	(literal) => t=literal {result = new OCLExpression(t);}
  	|   result = propertyCall[null]
    | 	LPAREN result=expression RPAREN 
    | 	t=ifExpression { result = new OCLExpression(t);}
    | 	TRUE { result=new OCLExpression(tb.tt()); }
    | 	FALSE { result=new OCLExpression(tb.ff()); }
    | 	NULL { result=new OCLExpression(tb.func(Op.NULL)); }
    {
    	if (result == null) {
    	    raiseError("Error in primary expression");
    	}
    }
  	;
  	
  	
ifExpression returns [Term result=null] throws SLTranslationException
{
	OCLExpression condition;
	OCLExpression branchA;
	OCLExpression branchB;
}
  	: 
  		IF condition = expression
    	THEN branchA = expression
	    ELSE branchB = expression
    	ENDIF
	    {
    		if (!condition.isTerm()) { raiseError("Wrong condition in if-then-else"); }
    		if (!branchA.isTerm()) { raiseError("error in then-branch"); }
    		if (!branchB.isTerm()) { raiseError("error in else-branch"); }
    		
    		try {
    		    result = tb.tf().createIfThenElseTerm(
    		        condition.getTerm(),
    		        branchA.getTerm(),
    		        branchB.getTerm());
    		} catch (AssertionError e) {
    		    raiseError("Wrong type in if-then-else-Term");
    		}
	    }
	;


literal returns [Term result=null] throws SLTranslationException
	:	STRING {raiseError("String literals are currently not supported.");}
	| 	n:NUMBER 
		{ 
		    Term intTerm = tb.zTerm(services, n.getText()); 
		    result = intHelper.castToLDTSort(intTerm, 
					 services.getTypeConverter()
					     	 .getIntLDT());
                }
//  |	enumLiteral //this looks just like a property call with a long name -> not good
  	{
  		if (result == null) {
  		    raiseError("Error in literal expression");
  		}
  	}
  	;


enumLiteral
  	:	NAME DCOLON NAME ( DCOLON NAME )*
  	;


literalCollection returns [OCLCollection resCollection=new OCLCollection()] throws SLTranslationException
{
	OCLCollection c1;
	int colType;
}	
    : 
		colType=collectionKind 
		LCURLY
    	(
    		resCollection=collectionItem[colType] 
    		(
        	    COMMA c1=collectionItem[colType]
        	    {
        	    	resCollection = resCollection.union(c1);
        	    }
    		)* 
    	)?
    	RCURLY
	;


collectionItem[int colType] returns [OCLCollection result=null] throws SLTranslationException
{
	OCLExpression t=null;
	OCLExpression a=null;
}
	:
		t=expression (DOTDOT a=expression)?
		{
			if(a==null) {
				result=new OCLCollection(t.getTerm(),colType);
			} else {
				// TODO: real error handling
				if(t.getTerm().sort()!=a.getTerm().sort()) {
					raiseError("TypeConformanceError:\n Types of a and b in 'a..b' are not identical");
				}
				
				Function leq=(Function) funcNS.lookup(new Name("leq"));
				result=new OCLCollection(t.getTerm(),a.getTerm(),leq,colType);
			}
		}
  	;


propertyCall[OCLExpression receiver] returns [OCLExpression result = null] throws SLTranslationException
{
	String propertyName = null;
	boolean atPre = false;
	boolean needVarDeclaration = false;
	OCLParameters parameters = null;
	ListOfOCLExpression qualifier;
}
	: 
       	propertyName=pathName
        (timeExpression {atPre = true;})?
        (qualifier=qualifiers {raiseError("qualifiers are not yet supported");})?
        {
        	needVarDeclaration = OCLResolverManager.needVarDeclaration(propertyName);
		}
        (parameters=propertyCallParameters[receiver, needVarDeclaration])?
        {
       	    result = (OCLExpression) OCLResolverManager.resolve(receiver, 
   								    		 propertyName, 
   									    	 parameters);
 
         	if(result == null) {
    			raiseError("The property call \"" + propertyName 
    					   + (parameters != null ? parameters.toString() : "") 
    					   + "\""
    					   + " on receiver \"" + receiver + "\""
    					   + " could not be resolved.");
        	}
        	
        	if(atPre) {
        	    if(preConditionParser) {
        	        raiseError("@pre not allowed in precondition!");
        	    }
				if(!result.isTerm()) {
        			raiseError("@pre is not supported "
        			           + "for types and collections.");
        		}
        		
    			Term t = convertToAtPre(result.getTerm());
        		result = new OCLExpression(t);
        	}

        	if(result.isTerm()) {
        		Term t = formulaBoolConverter.convertBoolToFormula(
	        												result.getTerm());
        		result = new OCLExpression(t);
        	}
        }
	;


propertyCallParameters[OCLExpression receiver, boolean needVarDeclaration]
		returns [OCLParameters result = null] throws SLTranslationException
{
	ListOfLogicVariable resultVars = SLListOfLogicVariable.EMPTY_LIST;
	ListOfOCLExpression resultEntities = SLListOfOCLExpression.EMPTY_LIST;
	
	Sort declaredVarsSort = (receiver == null ? null : receiver.getSort());
}
	:
		{
      		OCLResolverManager.pushLocalVariablesNamespace();
	    }
      	LPAREN 
      	(
      		(declarator[declaredVarsSort] BAR)=>
          	(
          		resultVars=declarator[declaredVarsSort] 
          		BAR
          		{
          			OCLResolverManager.putIntoTopLocalVariablesNamespace(resultVars);
          		}
          		resultEntities=actualParameterList
           	)
           	|
          	(
      			{
            	  	if(needVarDeclaration) {
            	  		LogicVariable collectionVar 
            	  				= ((OCLCollection) receiver.getCollection()).getPredVar();
        	  			OCLResolverManager.putIntoTopLocalVariablesNamespace(collectionVar);
        	  		    resultVars = resultVars.append(collectionVar);
    	      		}
          	  	}
              	resultEntities=actualParameterList
          	)? 
      	)
      	RPAREN	       	
  		{ 
    		OCLResolverManager.popLocalVariablesNamespace();
  			result = new OCLParameters(resultVars, resultEntities);
  		}
	;
	
	
declarator[Sort expectedSort] returns [ListOfLogicVariable result = null] throws SLTranslationException
{	
    ListOfString varNames=SLListOfString.EMPTY_LIST;
    KeYJavaType kjt=null;
    OCLExpression t;
}
	:
	  	{
			Debug.assertTrue(expectedSort != null);
	  	}
  		n1:NAME {varNames = varNames.append(n1.getText());}
     	(COMMA n2:NAME {varNames = varNames.append(n2.getText());})*
    	(COLON kjt=simpleTypeSpecifier)?
    	// Iterator not supported
    	(SEMICOL NAME COLON typeSpecifier EQUAL t=expression)?
    	{
    		Sort sort = (kjt == null ? expectedSort : kjt.getSort());
               
		    result = SLListOfLogicVariable.EMPTY_LIST;
            IteratorOfString it = varNames.iterator();    
            while(it.hasNext()) {
            	Name name = new Name(it.next());
            	result = result.append(new LogicVariable(name, sort));
            }
        }
  	;
  	
  	

typeSpecifier throws SLTranslationException
{
	KeYJavaType kjt;
}
  	: kjt=simpleTypeSpecifier
  	| collectionType
  	;


simpleTypeSpecifier returns [KeYJavaType result=null] throws SLTranslationException
{
	String s;
}
	:	s=pathName { result=javaInfo.getKeYJavaType(s); }
  	;


collectionType throws SLTranslationException
{
	KeYJavaType kjt;
	int colType;
}
	: 	colType=collectionKind LPAREN kjt=simpleTypeSpecifier RPAREN
  	;
  	
  	
actualParameterList returns [ListOfOCLExpression result=SLListOfOCLExpression.EMPTY_LIST] throws SLTranslationException
{
	OCLExpression t=null;
}
	: 
		t=expression { result=result.append(t); }
    	(COMMA t=expression { result=result.append(t); })*
	;


qualifiers returns [ListOfOCLExpression result=null] throws SLTranslationException
  	:	LBRACK result=actualParameterList RBRACK
  	;
  	

pathName returns [String result=""] throws SLTranslationException
	: 
		(n1:NAME DCOLON {result += n1.getText() + "."; })* n:NAME 
        {
        	if(result.length() > 0) {
        		//if the name does not stand for a type,
       			//replace the last "." with "::"
        		if(javaInfo.getTypeByClassName(result + n.getText()) == null) {
        			result = result.substring(0, result.length()-1) + "::";
        		}
        	}
        	result+=n.getText();
        } 
  	;


timeExpression
	: 	ATSIGN PRE
  	;



logicalOperator returns [Junctor result=null] throws SLTranslationException
	: 	AND     { result=Op.AND; }
  	| 	OR      { result=Op.OR; }
  	;


collectionKind returns [int colType=-1] throws SLTranslationException
 	:	SET        { colType=OCLCollection.OCL_SET; }
  	| 	BAG        { colType=OCLCollection.OCL_BAG; }
  	| 	SEQUENCE   { colType=OCLCollection.OCL_SEQUENCE; }
  	| 	COLLECTION { colType=-1; }
  	;

 
relationalOperator returns [Function result=null] throws SLTranslationException
	: 	GT { result = services.getTypeConverter().getIntegerLDT().getGreaterThan(); }
  	| 	LT { result = services.getTypeConverter().getIntegerLDT().getLessThan(); }
  	| 	GE { result = services.getTypeConverter().getIntegerLDT().getGreaterOrEquals(); }
  	| 	LE { result = services.getTypeConverter().getIntegerLDT().getLessOrEquals(); }
 	;

/*
addOperator returns [Operator result=null] throws SLTranslationException
  	: 	PLUS  { result = services.getTypeConverter().getIntegerLDT().getAdd(); }
  	| 	MINUS { result = services.getTypeConverter().getIntegerLDT().getSub(); }
  	;


multiplyOperator returns [Operator result=null] throws SLTranslationException
  	: 	MULT   { result = services.getTypeConverter().getIntegerLDT().getMul(); }
  	| 	DIVIDE { raiseError("reals are not supported ('/' is defined on real)"); }
  	;
*/
