// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.ArrayList;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
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
    public ConstructorCall(SchemaVariable newObjectSV,
			   ProgramElement consRef) {
	super(new Name("constructor-call"), consRef);
	this.newObjectSV = newObjectSV;
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

	New constructorReference = (New) pe;
	ProgramVariable newObject = 
	    (ProgramVariable) svInst.getInstantiation(newObjectSV);
	KeYJavaType classType = constructorReference.getTypeReference().getKeYJavaType();		

	System.out.println("constructorCall: classType: "+classType);
	
	final ExecutionContext ec = svInst.getExecutionContext();	
    
	if (!(classType.getJavaType() instanceof ClassDeclaration)) {
	    // no implementation available
	    return pe;
	}
	    
	
	final ArrayOfExpression arguments = 
	    constructorReference.getArguments();
	
	final ArrayList evaluatedArgs = new ArrayList();
    
	final ProgramVariable[] argumentVariables =  
	    new ProgramVariable[arguments.size()]; 	
               
	for (int i = 0, sz = arguments.size(); i<sz; i++) {
	    argumentVariables[i] = 
	        EvaluateArgs.evaluate(arguments.getExpression(i), evaluatedArgs, 
	                services, svInst.getExecutionContext());	  
	}
        
	final ProgramMethod method = services.getJavaInfo().
	  getProgramMethod(classType, NORMALFORM_IDENTIFIER, 
              (ProgramVariable[])argumentVariables, ec.
              getTypeReference().getKeYJavaType());
	
	Debug.assertTrue(method != null, "Call to non-existant constructor.");
    
	final MethodBodyStatement mbs = new MethodBodyStatement(method, newObject, null, 
               new ArrayOfExpression(argumentVariables)); 
    
	//   the assignment statements + the method body statement
	final Statement[] stmnts = new Statement[evaluatedArgs.size() + 1];
    
	for (int i = 0, sz=evaluatedArgs.size(); i<sz; i++) {
	    stmnts[i] = (Statement)evaluatedArgs.get(i); 
	}
	
	stmnts[stmnts.length-1] = mbs;
    
	return new StatementBlock(stmnts);
    	
    }

}
