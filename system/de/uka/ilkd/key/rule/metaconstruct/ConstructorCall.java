// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

/**
 * The constructor call meta construct is used to handle a allocation expression
 * like <code>new Class(...)</code>. Thereby it replaces the allocation 
 * expression by a method reference to an implict method called
 * <code>&lt;init&gt;</code> that is mainly the constructor but in its
 * normalform.
 */
public class ConstructorCall extends ProgramMetaConstruct {

    private static final String NORMALFORM_IDENTIFIER = 	    
		de.uka.ilkd.key.java.recoderext.
		 ConstructorNormalformBuilder.CONSTRUCTOR_NORMALFORM_IDENTIFIER;

    
    private final SchemaVariable newObjectSV;

    
    /** 
     * creates the metaconstruct
     */
    protected ConstructorCall(Name name, 
	    SchemaVariable newObjectSV,
	    ProgramElement consRef) {
	super(name, consRef);
	this.newObjectSV = newObjectSV;
    }
    
    /** 
     * creates the metaconstruct
     */
    public ConstructorCall(SchemaVariable newObjectSV,
			   ProgramElement consRef) {
	this(new Name("constructor-call"), newObjectSV, consRef);
    }

    /** 
     * transforms the constructor's body into its normalform and
     * returns the result. Thereby all necessary references are
     * resolved.
     * 
     * The method is optimized in the sense that insetad of returning
     * <code>newObject.<init>(args);</code>
     * a statementblock is returned which evaluates the constructor's arguments 
     * and inserts a method body statement rather than the method call which avoids 
     * unneccessary proof branches. As <code>newObject</code> can never be 
     * <code>null</code> no null pointer scheck is necessary.  
     */    
    public ProgramElement symbolicExecution
	(ProgramElement pe, Services services, SVInstantiations svInst) {

	final New constructorReference = (New) pe;	
	final KeYJavaType classType = constructorReference.getTypeReference().getKeYJavaType();			
    
	if (!(classType.getJavaType() instanceof ClassDeclaration)) {
	    // no implementation available
	    return pe;
	}
	
	final List<Statement> stmnts = constructorCallSequence(constructorReference,
                classType, svInst, services);
    
	return new StatementBlock(stmnts.toArray(new Statement[stmnts.size()]));
    	
    }

    /**
     * returns a sequence of statements modelling the Java constructor call semantics explicitly 
     */
    protected List<Statement> constructorCallSequence(
            final New constructorReference, final KeYJavaType classType,
            SVInstantiations svInst, Services services) {
	
	final ProgramVariable newObject = 
	    (ProgramVariable) svInst.getInstantiation(newObjectSV);
	final ExecutionContext ec = svInst.getExecutionContext();	
	final ImmutableArray<Expression> arguments = 
	    constructorReference.getArguments();
	
	final ArrayList<Statement> evaluatedArgs = new ArrayList<Statement>();
	
	int j=0;
	if(services.getJavaInfo().getAttribute(ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, classType)!=null){
	    j=1;
	}
	final ProgramVariable[] argumentVariables =  
	    new ProgramVariable[arguments.size()+j]; 	
               
	for (int i = 0, sz = arguments.size(); i<sz; i++) {
	    argumentVariables[i] = 
	        EvaluateArgs.evaluate(arguments.get(i), evaluatedArgs, 
	                services, ec);	  
	}
        
	if ( j == 1 ) {
            Sort s = services.getJavaInfo().getAttribute(ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, classType).sort();
	    Expression enclosingThis = (Expression) (constructorReference.getReferencePrefix() instanceof Expression?
	            constructorReference.getReferencePrefix() :
                        services.getTypeConverter().convertToProgramElement(
                                services.getTypeConverter().findThisForSort(s, ec)));
	    argumentVariables[argumentVariables.length-1] = 
	        EvaluateArgs.evaluate(enclosingThis, evaluatedArgs, 
	                        services, ec);    
	}
	
	ProgramMethod method = services.getJavaInfo().
	  getProgramMethod(classType, NORMALFORM_IDENTIFIER,
              argumentVariables, ec.
              getTypeReference().getKeYJavaType());
	
	Debug.assertTrue(method != null, "Call to non-existent constructor.");
    
	final MethodBodyStatement mbs = new MethodBodyStatement(method, newObject, null, 
               new ImmutableArray<Expression>(argumentVariables)); 
	
        //   the assignment statements + the method body statement + <allocateArea> for memory areas  
	final ArrayList<Statement> stmnts = new ArrayList<Statement>();

	for (int i = 0, sz=evaluatedArgs.size(); i<sz; i++) {
	    stmnts.add(evaluatedArgs.get(i));
	}               

        stmnts.add(mbs); 
	
	return stmnts;
    }

}
