// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
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
public final class StaticMethodCondition extends VariableConditionAdapter {

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

    private static ImmutableArray<Expression> toExpArray(ImmutableArray<? extends ProgramElement> a) {
	Expression[] result = new Expression[a.size()];
	for (int i=0; i<a.size(); i++) {
	    result[i]=(Expression)a.get(i);
	}
	return new ImmutableArray<Expression>(result);
    }


    @SuppressWarnings("unchecked")
    @Override
    public boolean check(SchemaVariable var,
			 SVSubstitute subst,
			 SVInstantiations svInst,
			 Services services) {

	ReferencePrefix rp = (ReferencePrefix) svInst.getInstantiation(caller);
	MethodName mn = (MethodName) svInst.getInstantiation(methname);
	ImmutableArray<ProgramElement> ape =
	    (ImmutableArray<ProgramElement>) svInst.getInstantiation(args);

	if (rp != null && mn != null && ape != null) {
	    ImmutableArray<Expression> ar
		= toExpArray((ImmutableArray<ProgramElement>)svInst.getInstantiation(args));
	    if (var == args) {
		ar = toExpArray((ImmutableArray<? extends ProgramElement>)subst);
	    }
	    ExecutionContext ec
		= svInst.getContextInstantiation().activeStatementContext();
	    MethodReference mr =new MethodReference(ar, mn, rp);
	    IProgramMethod method = null;
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


    @Override
    public String toString () {
	return (negation ? "\\not " : "") + "\\staticMethodReference(" + caller
	       + ", " + methname + ", " + args + ")";
    }
}