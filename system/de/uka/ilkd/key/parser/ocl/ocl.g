// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//


/* -*-antlr-*- */
header {
    package de.uka.ilkd.key.parser.ocl;

    import de.uka.ilkd.key.collection.IteratorOfString;
    import de.uka.ilkd.key.collection.ListOfString;
    import de.uka.ilkd.key.collection.SLListOfString;
    import de.uka.ilkd.key.java.abstraction.KeYJavaType;
    import de.uka.ilkd.key.java.abstraction.PrimitiveType;
    import de.uka.ilkd.key.java.JavaInfo;
    import de.uka.ilkd.key.java.Services;
    import de.uka.ilkd.key.logic.*;
    import de.uka.ilkd.key.logic.op.*;
    import de.uka.ilkd.key.logic.sort.*;
    import de.uka.ilkd.key.util.Debug;
    
    import java.lang.AssertionError;
    import java.util.Map;
    import java.util.HashMap;
}

class KeYOclParser extends Parser;

options {
	importVocab=KeYOclLexer;
	k=2;
	defaultErrorHandler=false;
}

{
    //constants
    private static final FunctionFactory funcFactory = FunctionFactory.INSTANCE;
    private static final TermBuilder tb = TermBuilder.DF;
    
    //parameters
    private Services services;
    private JavaInfo javaInfo;
    private Namespace funcNS;
    private Namespace sortNS;
    private Namespace varNS;
    
    //functions
    private Map localAtPreFunctions = new HashMap();
    
    //variables for variables
    private ParsableVariable selfVar;
    private ListOfParsableVariable paramVars;
    private ParsableVariable resultVar;
    private ParsableVariable excVar;
        
    //helper objects
    private FormulaBoolConverter formulaBoolConverter;
    private PropertyManager propertyManager;
    private AxiomCollector axiomCollector;
    
    private boolean preConditionParser;    

    /**
     * @param lexer the associated lexer
     */
    public KeYOclParser(TokenStream lexer,
 			Services services,  
                        AxiomCollector ac,
                        ParsableVariable selfVar,
                        ListOfParsableVariable paramVars,
                        ParsableVariable resultVar,
                        ParsableVariable excVar){
        this(lexer);
        
    	//save parameters        
        this.services = services;
        javaInfo = services.getJavaInfo();
        NamespaceSet nss = services.getNamespaces();
        funcNS   = nss.functions();
        sortNS   = nss.sorts();
        varNS    = nss.variables();
        this.selfVar   = selfVar;
        this.paramVars = paramVars;
        this.resultVar = resultVar;
        this.excVar    = excVar;
                
        //set axiomCollector
        axiomCollector = ac;
        
        //initialise formula-bool-converter
        formulaBoolConverter = new FormulaBoolConverter(services, nss);
        
        //initialise property manager
        propertyManager = new PropertyManager(services, formulaBoolConverter, excVar);
        propertyManager.pushLocalVariablesNamespace();
        if(selfVar != null) {
	        propertyManager.putIntoTopLocalVariablesNamespace(selfVar);
        }
        if(paramVars != null) {
			IteratorOfParsableVariable it = paramVars.iterator(); 
			while(it.hasNext()) {
				propertyManager.putIntoTopLocalVariablesNamespace(it.next());
			}
        }
        if(resultVar != null) {
		 	propertyManager.putIntoTopLocalVariablesNamespace(resultVar);
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
    
    private void raiseError(String message) throws OCLTranslationError {
    	throw new OCLTranslationError("OCL Parser Error: " + message, getLine(), getColumn());
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
     * Helper for buildAtPreDefinition().
     */
    private Term[] getTerms(ArrayOfQuantifiableVariable vars) {
        int numVars = vars.size();
        Term[] result = new Term[numVars];

        for(int i = 0; i < numVars; i++) {
            LogicVariable var
                    = (LogicVariable)(vars.getQuantifiableVariable(i));
            result[i] = tb.var(var);
        }

        return result;
    }


    /**
     * Creates a definition for an atPre function
     * (helper for convertToAtPre()).
     * @param f1 original function
     * @param f2 atPre function
     */
    protected Term buildAtPreDefinition(Operator f1, Function f2) {
        Term result = tb.tt();

	    int arity = f1.arity();
	    assert arity == f2.arity();
	    LogicVariable[] args = new LogicVariable[arity];
	    for(int i = 0; i < arity; i++) {
	        args[i] = new LogicVariable(new Name("x" + i), f2.argSort(i));
	    }
	
	    Term[] argTerms = getTerms(new ArrayOfQuantifiableVariable(args));
	
	    Term f1Term = TermFactory.DEFAULT.createTerm(f1,
	                                argTerms,
	                                (ArrayOfQuantifiableVariable)null,
	                                null);
	    Term f2Term = tb.func(f2, argTerms);
	    Term equalsTerm = tb.equals(f1Term, f2Term);
	    Term quantifTerm;
	    if(arity > 0) {
	        quantifTerm = tb.all(args, equalsTerm);
	    } else {
	        quantifTerm = equalsTerm;
	    }
	    result = tb.and(result, quantifTerm);	    
        return result;
    }
    
        
    
    /**
     * Converts a term so that it's top-level operator refers to the pre-state.
     * Creates and saves new atPreFunctions when necessary.
     */
    private Term convertToAtPre(Term term) {
		Term[] subTerms = getSubTerms(term);
		
		Function atPreFunction = (Function) localAtPreFunctions.get(term.op());
		if(atPreFunction == null) {
			String name = term.op().name().toString() + "@pre";
			if(name.startsWith(".")) {
				name = name.substring(1);
			}
			atPreFunction = new RigidFunction(new Name(name),
											  term.sort(),
											  getSorts(subTerms));
			localAtPreFunctions.put(term.op(), atPreFunction);
			funcNS.add(atPreFunction);
			axiomCollector.collectAxiom(atPreFunction, 
										buildAtPreDefinition(term.op(), 
															 atPreFunction));
		}
		
		Term result = tb.func(atPreFunction, subTerms);
		return result;	
    }
    
    
    /**
     * Builds a term representing equality among two OCLEntities
     * depending on their type. If the types are not compatible,
     * null is returned.
     */
    private Term buildEqualityTermByEntity(OCLEntity a, OCLEntity b)
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
			Sort csort = a.getCollection().getFunctionalRestriction().sort();
			LogicVariable v = new LogicVariable(
			    //TODO: change variable-name
			    new Name("e"),
                ((AbstractCollectionSort) csort).elementSort());
			if(a.getCollection().isSet() && b.getCollection().isSet()) {
				Function isIn = (Function) funcNS.lookup(new Name(csort.name().toString()+"::includes"));
				Term subTerm = tb.equiv(
				    tb.func(isIn,
				        a.getCollection().getFunctionalRestriction(),
				        tb.var(v)),
				    tb.func(isIn,
				        b.getCollection().getFunctionalRestriction(),
				        tb.var(v)));
				result = tb.all(v,subTerm);
			}
			if(a.getCollection().isBag() && b.getCollection().isBag()) {
				Function count = (Function) funcNS.lookup(new Name(csort.name().toString()+"::count"));
				Term subTerm = tb.equiv(
				    tb.func(count,
				        a.getCollection().getFunctionalRestriction(),
				        tb.var(v)),
				    tb.func(count,
				        b.getCollection().getFunctionalRestriction(),
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
    public Term parseExpression() throws OCLTranslationError {
        
    	OCLEntity expr = null;
    	try {
          expr = expression();
    	} catch(RecognitionException e) {
    		if (e instanceof OCLTranslationError)
    			throw (OCLTranslationError)e;
    	    else
    	        throw new OCLTranslationError(
    	            ((antlr.RecognitionException)e).getMessage(),
    	            ((antlr.RecognitionException)e).getLine(),
    	            ((antlr.RecognitionException)e).getColumn());
    	} catch (ANTLRException e) {
    	    raiseError("Unknown OCL-Translation error (from ANTLR): " + e.getMessage());
    	} catch (Exception e) {
    	    raiseError("OCL-Translation error: " + e.getMessage());
    	}
        
        if(expr == null) {
            raiseError("OCL-Translation error.");
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

top 
{
	OCLEntity t;
}
	: 
		t = oclExpression 
	    { 
    		Debug.fail("Should be never entered. Only workaround of an antlr bug."); 
	    }
	;


oclFile
	: 	( "package" packageName oclExpressions "endpackage" )+
	;


packageName
{
	String s;
}
	: 	s=pathName
	;


oclExpressions
	:	(constraint)*
	;


constraint
{
	OCLEntity t;
}
	: 
		contextDeclaration 
	    (   
	    	("def" (NAME)? COLON (letExpression)*)
    	    | 
    	    (stereotype (NAME)? COLON t=oclExpression)
	    )+
	;


contextDeclaration
	: 
		"context" (operationContext | classifierContext)
	;


classifierContext
	: 	(NAME COLON NAME)
	| 	NAME
	;


operationContext
	: 
		NAME DCOLON operationName LPAREN formalParameterList RPAREN
	    ( COLON returnType )?
	;


returnType
  	: 	typeSpecifier
  	;


stereotype
    :	"pre"
	| 	"post"
    | 	"inv"
    ;


operationName
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


oclExpression returns [OCLEntity result=null]
  	:	( (letExpression)* "in" )?  result=expression
  	;
  	

letExpression
{
	OCLEntity t;
}
  	: 
  		"let" NAME 
  		//( LPAREN formalParameterList RPAREN )?         // not allowed anymore in OCL2.0
    	( COLON typeSpecifier )?
    	EQUAL t=expression
  	;
  	
  	
formalParameterList
  	: 
  		( 
  			NAME COLON typeSpecifier 
      		(COMMA NAME COLON typeSpecifier)*
    	)?
  	;  	




//-----------------------------------------------------------------------------
//Rules for expressions and below
//-----------------------------------------------------------------------------

expression returns [OCLEntity result=null]
  	: result=implicationExpression
  	;


implicationExpression returns [OCLEntity result=null]
{
	OCLEntity a=null;
}
  	: 
  		result=logicalExpression
        ( 
           	IMPLIES a=logicalExpression
            {
                result = new OCLEntity(
                    tb.imp(result.getTerm(),a.getTerm()));
            }
        )* 
	;


logicalExpression returns [OCLEntity result=null]
{
	OCLEntity a=null;
	Junctor j=null;
}
  	: 
  		result=relationalExpression
        ( 
            (XOR relationalExpression) => XOR a=relationalExpression
            {
                result = new OCLEntity(
                    tb.not(
                        tb.equals(
                            result.getTerm(),
                            a.getTerm())));
            }
            |
           	j=logicalOperator a=relationalExpression
            {
                result = new OCLEntity(
                    tb.tf().createJunctorTermAndSimplify(
                        j,
                        result.getTerm(),
                        a.getTerm()));
            }
        )* 
	;


relationalExpression returns [OCLEntity result=null]
{
	OCLEntity a=null;
	Function f=null;
}
	: 
		result=additiveExpression
	    ( 
            (EQUAL additiveExpression) => EQUAL a=additiveExpression 
	        {
    			result = new OCLEntity(
    			    buildEqualityTermByEntity(result,a));
	        }
            | 
            (NEQUAL additiveExpression) => NEQUAL a=additiveExpression
            {
    			result = new OCLEntity(
    			    tb.not(
    			        buildEqualityTermByEntity(result,a)));

    	    }  
            | 
            f=relationalOperator a=additiveExpression 
            {
            	result = new OCLEntity(
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


additiveExpression returns [OCLEntity result=null]
{
	OCLEntity a=null;
	Operator op=null; 
}
  	: 
  		result=multiplicativeExpression
	    ( 
	    	op=addOperator a=multiplicativeExpression 
    		{
      			result = new OCLEntity(
      			    tb.func(
      			        (Function) op,
      			        result.getTerm(),
      			        a.getTerm()));
	    	}
    	)*
	;


multiplicativeExpression returns [OCLEntity result=null]
{
	OCLEntity a=null;
    Operator op=null; 
}
  	: 
  		result=unaryExpression
	    ( 
	    	op=multiplyOperator a=unaryExpression 
      		{
      			result = new OCLEntity(
      			    tb.func(
      			        (Function) op,
      			        result.getTerm(),
      			        a.getTerm()));
      		}
	    )*
  	;


unaryExpression returns [OCLEntity result=null]
	: 
		(NOT postfixExpression) => NOT result=postfixExpression
	    {
    		result = new OCLEntity(
    		    tb.not(result.getTerm()));
	    }
		| 
		(MINUS postfixExpression) => MINUS result=postfixExpression
    	{
    		Function neg = (Function) funcNS.lookup(new Name("neg"));
    		result = new OCLEntity(
    		    tb.func(neg,result.getTerm()));
    	}
  		| 
  		result=postfixExpression
  	;


postfixExpression returns [OCLEntity result=null]
{
	OCLEntity entity=null;
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
  
  
primaryExpression returns [OCLEntity result=null]
{
	Term t;
	OCLCollection c;
}
  	:   c=literalCollection { result = new OCLEntity(c); }
  	| 	(literal) => t=literal {result = new OCLEntity(t);}
  	|   result = propertyCall[null]
    | 	LPAREN result=expression RPAREN 
    | 	t=ifExpression { result = new OCLEntity(t);}
    | 	TRUE { result=new OCLEntity(tb.tt()); }
    | 	FALSE { result=new OCLEntity(tb.ff()); }
    | 	NULL { result=new OCLEntity(tb.func(Op.NULL)); }
    {
    	if (result == null) {
    	    raiseError("Error in primary expression");
    	}
    }
  	;
  	
  	
ifExpression returns [Term result=null]
{
	OCLEntity condition;
	OCLEntity branchA;
	OCLEntity branchB;
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


literal returns [Term result=null]
	:	STRING {raiseError("String literals are currently not supported.");}
	| 	n:NUMBER { result=tb.zTerm(services, n.getText()); }
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


literalCollection returns [OCLCollection resCollection=new OCLCollection()]
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


collectionItem[int colType] returns [OCLCollection result=null]
{
	OCLEntity t=null;
	OCLEntity a=null;
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


propertyCall[OCLEntity receiver] returns [OCLEntity result = null]
{
	String propertyName = null;
	boolean atPre = false;
	boolean needVarDeclaration = false;
	OCLParameters parameters = null;
	ListOfOCLEntity qualifier;
}
	: 
       	propertyName=pathName
        (timeExpression {atPre = true;})?
        (qualifier=qualifiers {raiseError("qualifiers are not yet supported");})?
        {
        	needVarDeclaration = propertyManager.needVarDeclaration(propertyName);
		}
        (parameters=propertyCallParameters[receiver, needVarDeclaration])?
        {
        	result = propertyManager.resolve(receiver, 
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
        		result = new OCLEntity(t);
        	}

        	if(result.isTerm()) {
        		Term t = formulaBoolConverter.convertBoolToFormula(
	        												result.getTerm());
        		result = new OCLEntity(t);
        	}
        }
	;


propertyCallParameters[OCLEntity receiver, boolean needVarDeclaration] 
		returns [OCLParameters result = null]
{
	ListOfLogicVariable resultVars = SLListOfLogicVariable.EMPTY_LIST;
	ListOfOCLEntity resultEntities = SLListOfOCLEntity.EMPTY_LIST;
	
	Sort declaredVarsSort = (receiver == null ? null : receiver.getSort());
}
	:
		{
      		propertyManager.pushLocalVariablesNamespace();
	    }
      	LPAREN 
      	(
      		(declarator[declaredVarsSort] BAR)=>
          	(
          		resultVars=declarator[declaredVarsSort] 
          		BAR
          		{
          			propertyManager.putIntoTopLocalVariablesNamespace(resultVars);
          		}
          		resultEntities=actualParameterList
           	)
           	|
          	(
      			{
            	  	if(needVarDeclaration) {
            	  		LogicVariable collectionVar 
            	  				= receiver.getCollection().getPredVar();
        	  			propertyManager.putIntoTopLocalVariablesNamespace(collectionVar);
        	  		    resultVars = resultVars.append(collectionVar);
    	      		}
          	  	}
              	resultEntities=actualParameterList
          	)? 
      	)
      	RPAREN	       	
  		{ 
    		propertyManager.popLocalVariablesNamespace();
  			result = new OCLParameters(resultVars, resultEntities);
  		}
	;
	
	
declarator[Sort expectedSort] returns [ListOfLogicVariable result = null]
{	
    ListOfString varNames=SLListOfString.EMPTY_LIST;
    KeYJavaType kjt=null;
    OCLEntity t;
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
  	
  	

typeSpecifier
{
	KeYJavaType kjt;
}
  	: kjt=simpleTypeSpecifier
  	| collectionType
  	;


simpleTypeSpecifier returns [KeYJavaType result=null]
{
	String s;
}
	:	s=pathName { result=javaInfo.getKeYJavaType(s); }
  	;


collectionType
{
	KeYJavaType kjt;
	int colType;
}
	: 	colType=collectionKind LPAREN kjt=simpleTypeSpecifier RPAREN
  	;
  	
  	
actualParameterList returns [ListOfOCLEntity result=SLListOfOCLEntity.EMPTY_LIST]
{
	OCLEntity t=null;
}
	: 
		t=expression { result=result.append(t); }
    	(COMMA t=expression { result=result.append(t); })*
	;


qualifiers returns [ListOfOCLEntity result=null]
  	:	LBRACK result=actualParameterList RBRACK
  	;
  	

pathName returns [String result=""]
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



logicalOperator returns [Junctor result=null]
	: 	AND     { result=Op.AND; }
  	| 	OR      { result=Op.OR; }
  	;


collectionKind returns [int colType=-1]
 	:	SET        { colType=OCLCollection.OCL_SET; }
  	| 	BAG        { colType=OCLCollection.OCL_BAG; }
  	| 	SEQUENCE   { colType=OCLCollection.OCL_SEQUENCE; }
  	| 	COLLECTION { colType=-1; }
  	;

 
relationalOperator returns [Function result=null]
	: 	GT { result = (Function) funcNS.lookup(new Name("gt")); }
  	| 	LT { result = (Function) funcNS.lookup(new Name("lt")); }
  	| 	GE { result = (Function) funcNS.lookup(new Name("geq")); }
  	| 	LE { result = (Function) funcNS.lookup(new Name("leq")); }
 	;


addOperator returns [Operator result=null]
  	: 	PLUS  { result = (Function) funcNS.lookup(new Name("add")); }
  	| 	MINUS { result = (Function) funcNS.lookup(new Name("sub")); }
  	;


multiplyOperator returns [Operator result=null]
  	: 	MULT   { result = (Function) funcNS.lookup(new Name("mul")); }
  	| 	DIVIDE { raiseError("reals are not supported ('/' is defined on real)"); }
  	;
  	
