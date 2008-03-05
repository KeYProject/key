// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.metaconstruct;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.operator.Instanceof;
import de.uka.ilkd.key.java.expression.operator.NewArray;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;


/** 
 * Symbolically executes a method invocation
 */ 
public class MethodCall extends ProgramMetaConstruct {



    private final SchemaVariable resultVar;
    
    protected MethodReference methRef;
    private ProgramMethod pm;
    protected ReferencePrefix newContext;
    private Services services;
    protected ProgramVariable pvar;
    private IExecutionContext execContextSV;
    private ExecutionContext execContext;
    protected ArrayOfExpression arguments;
    protected KeYJavaType staticPrefixType;

    /** creates the methodcall-MetaConstruct 
     * @param body the ProgramElement contained by the meta construct 
     */
    public MethodCall(ProgramElement body) {
	this(null, null, body);
    }

    
    /** creates the methodcall-MetaConstruct 
     * @param result the SchemaVariable that is used to keep the result
     * @param body the ProgramElement contained by the meta construct 
     */
    public MethodCall(SchemaVariable result, ProgramElement body) {
	this(null, result, body);
    }

    /** creates the methodcall-MetaConstruct 
     * @param result the SchemaVariable that is used to keep the result
     * @param body the ProgramElement contained by the meta construct 
     */
    public MethodCall(ProgramSV ec, SchemaVariable result,
		      ProgramElement body) {
        this(new Name("method-call"), ec, result, body);
    }

    /** creates the methodcall-MetaConstruct 
     * @param result the SchemaVariable that is used to keep the result
     * @param body the ProgramElement contained by the meta construct 
     */
    protected MethodCall(Name name, ProgramSV ec, 
                         SchemaVariable result,
                         ProgramElement body) {
        super(name, body);
        this.resultVar = result;
        this.execContextSV = ec;
    }
    

    /** gets an array of expression and returns a list of types */
    private ListOfKeYJavaType getTypes(ArrayOfExpression args) {        
        ListOfKeYJavaType result = SLListOfKeYJavaType.EMPTY_LIST; 
	for (int i = args.size()-1; i >= 0 ; i--) {
	    Expression argument = args.getExpression(i);
	    result = result.prepend
		(services.getTypeConverter().getKeYJavaType(argument, execContext));
	}
	return result;
    }


    private ProgramMethod assertImplementationPresent(ProgramMethod method,
						      KeYJavaType t) {
	if (method == null) {	    
	    Debug.fail("methodcall:No implementation available for ", method);
	}
	return method;
    }


    private KeYJavaType getStaticPrefixType(ReferencePrefix refPrefix) {
	if (refPrefix==null || refPrefix instanceof ThisReference && 
	        ((ThisReference) refPrefix).getReferencePrefix()==null){ 
	    return execContext.getTypeReference().getKeYJavaType();
	} else if(refPrefix instanceof ThisReference){
	    return ((TypeReference) ((ThisReference) refPrefix).getReferencePrefix()).getKeYJavaType();
	    //((ProgramVariable) services.getTypeConverter().convertToLogicElement(refPrefix).op()).getKeYJavaType();
	}else if (refPrefix instanceof TypeRef) {
	    KeYJavaType t = ((TypeRef)refPrefix).getKeYJavaType();
	    if (t == null) { //%%%
		Debug.fail();
	    }
	    return t;
	} else if (refPrefix instanceof ProgramVariable) {
	    return ((ProgramVariable)refPrefix).getKeYJavaType();
	} else if (refPrefix instanceof FieldReference) {
	    return ((FieldReference)refPrefix).getProgramVariable()
		.getKeYJavaType();
	} else if (refPrefix instanceof SuperReference) {
	    KeYJavaType st = services.getJavaInfo().getSuperclass
                (execContext.getTypeReference().getKeYJavaType());
	    return st; 	
	} else {
	    throw new de.uka.ilkd.key.util.NotSupported
		("Unsupported method invocation mode\n"+
		 refPrefix.getClass());
	}			    
    }

    protected ProgramMethod getMethod(KeYJavaType prefixType, MethodReference mr) {
	ProgramMethod result;
 	if (execContext != null){
	    result = mr.method(services, prefixType, execContext);
	    if (result == null) {
		// if a method is declared protected and prefix and
		// execContext are in different packages we have to
		// simulate visibility rules like being in prefixType
		result = mr.method(services, prefixType, 
		        mr.getMethodSignature(services, execContext), prefixType);
	    }
 	} else {
	    result = mr.method(services, prefixType, 
	            mr.getMethodSignature(services, execContext), prefixType);
 	}
	return result;
    }


    private ProgramMethod getSuperMethod(ExecutionContext ex,
					 MethodReference mr) {
	return mr.method(services, getSuperType(ex), ex);
    }

    private KeYJavaType getSuperType(ExecutionContext ex) {
	return services.getJavaInfo().getSuperclass
	    (ex.getTypeReference().getKeYJavaType());
    }
    

    /** performs the program transformation needed for symbolic
     * program execution 
     * @param services the Services with all necessary information 
     * about the java programs
     * @param svInst the instantiations esp. of the inner and outer label 
     * @return the transformed program
     */
    public ProgramElement symbolicExecution(ProgramElement pe,
					    Services services,
					    SVInstantiations svInst) {

	Debug.out("method-call: called for ", pe);
	this.services=services;

	if (resultVar != null) {
	    pvar = (ProgramVariable) svInst.getInstantiation(resultVar);
	}

	if (execContextSV!=null) {
	    execContext
		= (ExecutionContext) svInst.getInstantiation
		((SortedSchemaVariable)execContextSV);
	} else {
	    execContext = svInst.getContextInstantiation().activeStatementContext();
	}

	methRef = (MethodReference) pe;

	ReferencePrefix refPrefix = methRef.getReferencePrefix();
	if (refPrefix == null) {
	    if (execContext.getRuntimeInstance() == null) {
		refPrefix = execContext.getTypeReference();
	    } else {
		refPrefix = execContext.getRuntimeInstance();
	    }
	}
	
	staticPrefixType = getStaticPrefixType(methRef.getReferencePrefix());
	if(execContext != null){
	    pm = assertImplementationPresent
		(methRef.method(services, staticPrefixType, execContext),
		 staticPrefixType);
	}else{
	    pm = assertImplementationPresent
		(methRef.method(services, staticPrefixType, 
		        methRef.getMethodSignature(services, null), 
		        staticPrefixType), 
		 staticPrefixType);	    
	}
        newContext = methRef.getReferencePrefix();
	if (newContext == null){
	    Term self = services.getTypeConverter().findThisForSort(pm.getContainerType().getSort(), execContext);
	    if(self!=null){
	        newContext = (ReferencePrefix) services.getTypeConverter().convertToProgramElement(self);
	    }
	} else if(newContext instanceof ThisReference){
	    newContext = (ReferencePrefix) services.getTypeConverter().convertToProgramElement(
                services.getTypeConverter().convertToLogicElement((ThisReference) newContext, execContext));
	} else if (newContext instanceof FieldReference) {
	    final FieldReference fieldContext = (FieldReference) newContext;
            if (fieldContext.referencesOwnInstanceField())
	        newContext = fieldContext.setReferencePrefix
		    (execContext.getRuntimeInstance());
	}
	
	VariableSpecification[] paramSpecs = createParamSpecs();
	Statement[] paramDecl = createParamAssignments(paramSpecs);


        arguments = getVariables(paramSpecs);

	Statement result = null;
	
	if (pm.isStatic()) {	// Static invocation mode
	    Debug.out("method-call: invocation of static method detected");
            newContext = null;
	    ProgramMethod staticMethod = getMethod(staticPrefixType, methRef);	                
            result = new MethodBodyStatement(staticMethod, newContext,
					     pvar, arguments); 
	} else if (refPrefix instanceof SuperReference) {
	    Debug.out("method-call: super invocation of method detected." + 
		      "Requires static resolving.");
	    ProgramMethod superMethod = getSuperMethod(execContext,
						       methRef);
	    result = new MethodBodyStatement
		(superMethod, execContext.getRuntimeInstance(), pvar,
		 arguments);
	} else {    // Instance invocation mode
	    if (pm.isPrivate()) { // private methods are bound statically
		Debug.out("method-call: invocation of private method detected." + 
			  "Requires static resolving.");
                result = makeMbs(staticPrefixType);
	    } else {
		Debug.out("method-call: invocation of non-private"
			  +" instance method detected." 
			  +"Requires dynamic resolving.");
		ListOfKeYJavaType imps = 
		    services.getJavaInfo().getKeYProgModelInfo().findImplementations
		    (staticPrefixType, methRef.getName(), getTypes(arguments));
		if (imps.isEmpty()) {
		    imps = services.getJavaInfo().getKeYProgModelInfo().findImplementations
	                    (pm.getContainerType(), methRef.getName(), getTypes(arguments));
		}
		if (imps.isEmpty()) {
		    Type staticPrefix = staticPrefixType.getJavaType();
		    if (staticPrefix instanceof ClassType &&
		       (((ClassType)staticPrefix).isInterface() || 
		        ((ClassType)staticPrefix).isAbstract()) ) {
			// no implementing sub type found
                        // insert mbs with interface type so that contracts are applicable
			result = makeMbs(staticPrefixType);
		    }
		} else {
		    result = makeIfCascade(imps);
		}
	    }
	}
	return KeYJavaASTFactory.
	    insertStatementInBlock(paramDecl, new StatementBlock(result));
    }


    //***************** Dynamic Binding Construction Utilities ***************


    private Statement makeMbs(KeYJavaType t) {
	ProgramMethod meth = getMethod(t, methRef);
	return new MethodBodyStatement(meth, newContext,
				       pvar, arguments);
    }

    public Expression makeIOf(Type t) {
	Debug.assertTrue(newContext!=null);
	return new Instanceof((Expression) newContext, 
			      new TypeRef((KeYJavaType)t));
    }


    protected Statement makeIfCascade(ListOfKeYJavaType imps) {
        KeYJavaType currType = imps.head();
        if (imps.size()==1) 
           return makeMbs(currType);
        else return new If(makeIOf(currType),
                           new Then(makeMbs(currType)),
                           new Else(makeIfCascade(imps.tail())));
    }


    public VariableSpecification[] createParamSpecs(){
	
	MethodDeclaration methDecl    = pm.getMethodDeclaration();
	int params                    = methDecl.getParameterDeclarationCount();
	VariableSpecification[] varSpecs = new VariableSpecification[params];
	for (int i = 0; i < params; i++) {
	    ParameterDeclaration parDecl =
		methDecl.getParameterDeclarationAt(i);
	    VariableSpecification originalSpec =
		parDecl.getVariableSpecification();
	    final ProgramVariable originalParamVar =
	        (ProgramVariable)originalSpec.getProgramVariable ();

            VariableNamer varNamer = services.getVariableNamer();
	    ProgramElementName newName 
	    	= varNamer.getTemporaryNameProposal(originalParamVar
					  .getProgramElementName().toString());

	    final IProgramVariable paramVar
	    	= new LocationVariable(newName,
	    			      originalParamVar.getKeYJavaType());

	    if(i == params-1 && methDecl.isVarArgMethod() &&
	            (   methRef.getArguments().size() != params 
	             || notCompatible(methRef.getArgumentAt(i), originalSpec.getType()))) {
	        // variable argument
	        varSpecs[i] = new VariableSpecification(paramVar, 1, makeVariableArgument(originalSpec), originalSpec.getType());
	    } else {
	        // normal argument
	        varSpecs[i] =
	            new VariableSpecification
	                    (paramVar, 
	                    originalSpec.getDimensions(), 
	                    methRef.getArgumentAt(i),
	                    originalSpec.getType());
	    }
	} 
	return varSpecs;
    }

    
    private Expression makeVariableArgument(VariableSpecification originalSpec) {
        
        int params = pm.getMethodDeclaration().getParameterDeclarationCount();
        int args = methRef.getArguments().size();
        Expression[] exps = new Expression[args - params + 1];
                                           
        for (int i = 0; i < exps.length; i++) {
            exps[i] = methRef.getArgumentAt(params - 1 + i);
        }
        
        Type type = originalSpec.getType();
        KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(type);
        TypeRef tyref = new TypeRef(kjt);
        
        ArrayInitializer arrayInit = new ArrayInitializer(exps);
        Expression[] emptyArgs = new Expression[0];
        NewArray newArray = new NewArray(emptyArgs, tyref, kjt, arrayInit, 1);
        
        return newArray;
    }


    public Statement[] createParamAssignments(VariableSpecification[] specs) {
	MethodDeclaration methDecl    = pm.getMethodDeclaration();
	Statement[] paramDecl = new Statement[specs.length];
	for (int i=0; i<specs.length; i++) {
	    ParameterDeclaration parDecl = 
		methDecl.getParameterDeclarationAt(i);
	    paramDecl[i] = new LocalVariableDeclaration
		(parDecl.getModifiers(), parDecl.getTypeReference(), specs[i]);
	}
	return paramDecl;
    }

    private ArrayOfExpression getVariables(VariableSpecification[] varspecs) {
	Expression[] vars = new Expression[varspecs.length];
	for (int i=0; i<varspecs.length; i++) {
	    vars[i] = (Expression) varspecs[i].getProgramVariable();
	}
	return new ArrayOfExpression(vars);
    }
    
    /**
     * check whether an expression is assignment-compatible with a type.
     * 
     * In the absence of autoboxing this is the case if the type is a subtype.
     * 
     * @param exp expression to check
     * @param type type to check for
     * @return true iff exp is assign compatible with type 
     */
    private boolean notCompatible(Expression exp, Type type) {
        KeYJavaType expKJT = exp.getKeYJavaType(services, execContext);
        KeYJavaType typeKJT = services.getJavaInfo().getKeYJavaType(type); 
        return services.getJavaInfo().isSubtype(expKJT, typeKJT);
    }

	

}
