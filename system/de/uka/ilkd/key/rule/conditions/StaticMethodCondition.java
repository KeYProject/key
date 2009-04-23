// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.conditions;


import de.uka.ilkd.key.java.ArrayOfExpression;
import de.uka.ilkd.key.java.ArrayOfProgramElement;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * ensures that the given instantiation for the schemavariable denotes
 * a static method. For determining the method the callee and the
 * arguments of the method are needed as arguments.
 */
public class StaticMethodCondition extends VariableConditionAdapter {

    private final boolean negation;
    private final SchemaVariable caller;
    private final SchemaVariable methname;
    private final SchemaVariable args;

    /**
     * the static reference condition checks if a suggested
     * instantiation for a schema variable denotes a static method
     * call. The flag negation allows to reuse this condition for
     * ensuring non static references.
     */
    public StaticMethodCondition (boolean negation, 
				  SchemaVariable caller, 
				  SchemaVariable methname,
				  SchemaVariable args) {
	this.negation = negation;
	this.caller = caller;
	this.methname = methname;
	this.args = args;
    }

    private static ArrayOfExpression toArrayOfExpression
	(ArrayOfProgramElement a) {
	Expression[] result = new Expression[a.size()];
	for (int i=0; i<a.size(); i++) {
	    result[i]=(Expression)a.getProgramElement(i);
	}
	return new ArrayOfExpression(result);
    }

    /**
     * tests if the instantiation suggestions goes along with the static
     * condition
     * @param var the template Variable to be instantiated
     * @param subst the SVSubstitute to be mapped to var
     * @param svInst the SVInstantiations that are already known to be
     * needed
     * @return true iff condition is fulfilled
     */
    public boolean check(SchemaVariable var, 
			 SVSubstitute subst, 
			 SVInstantiations svInst,
			 Services services) {
	
	ReferencePrefix rp = (ReferencePrefix) svInst.getInstantiation(caller);
	MethodName mn = (MethodName) svInst.getInstantiation(methname);
	ArrayOfProgramElement ape = 
	    (ArrayOfProgramElement) svInst.getInstantiation(args);

	if (rp != null && mn != null && ape != null) {
	    ArrayOfExpression ar 
		= toArrayOfExpression((ArrayOfProgramElement) 
				      svInst.getInstantiation(args));
	    if (var==args) {
                assert subst instanceof ArrayOfExpression : 
                    "wrong use of StaticMethodCondition";
		ar = (ArrayOfExpression) subst;
	    }
	    ExecutionContext ec 
		= svInst.getContextInstantiation().activeStatementContext();
	    MethodReference mr =new MethodReference(ar, mn, rp);
	    ProgramMethod method = null;
	    KeYJavaType prefixType = services.getTypeConverter().
		getKeYJavaType((Expression) rp, ec);
	    if((rp instanceof LocationVariable) && 
	       (((LocationVariable) rp).sort() instanceof NullSort)){
		return true;
	    }
	    if (ec!=null) {
		method = mr.method(services, prefixType, ec);
		// we are only interested in the signature. The method
		// must be declared in the static context.
	    } else { //no execution context
		method = mr.method (services, prefixType, 
		        mr.getMethodSignature(services, ec),
		        prefixType);
	    }
	    if (method == null) {	
		return false;		
	    }
	    return negation ^ method.isStatic();
	}
	return true;
    }

    public String toString () {
	return (negation ? "\\not " : "") + "\\staticMethodReference(" + caller + ", " + methname + ", " + args + ")";
    }

}
