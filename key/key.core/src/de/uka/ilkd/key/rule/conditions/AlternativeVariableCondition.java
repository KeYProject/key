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


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * disjoin two variable conditions
 * @author bruns
 */
public final class AlternativeVariableCondition
    <U extends VariableConditionAdapter, V extends VariableConditionAdapter> 
    extends VariableConditionAdapter {

	private final U delegate0;
	private final V delegate1;

    public AlternativeVariableCondition (U delegate0, V delegate1) {
    	this.delegate0 = delegate0;
    	this.delegate1 = delegate1;
    }

    /**
     * check whether any of the two delegates apply
     */
    @Override
    public boolean check(SchemaVariable var, 
                    SVSubstitute subst, 
                    SVInstantiations svInst,
                    Services services) {
    	return delegate0.check(var, subst, svInst, services)
    			|| delegate1.check(var, subst, svInst, services);

    }


    @Override
    public String toString () {
        return "\\or("+delegate0+","+delegate1+")";
    }
}