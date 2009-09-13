// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// This file is part of KeY - Integrated Deductive Software Design

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
* Ensures the same heap dependent predicate
*/

public class SameHeapDependentPredicateVariableCondition extends VariableConditionAdapter {

private SchemaVariable s1, s2;

public SameHeapDependentPredicateVariableCondition(SchemaVariable s1, SchemaVariable s2) {
this.s1 = s1;
this.s2 = s2;
}

public boolean check(SchemaVariable var, SVSubstitute instCandidate, 
				  SVInstantiations instMap, Services services) {

	Term f1 = (Term) instMap.getInstantiation(s1);
	Term f2 = (Term) instMap.getInstantiation(s2);
	
	if (f1.op() instanceof IUpdateOperator) {
	f1 = ((IUpdateOperator) f1.op()).target(f1);
	} 

	if (f2.op() instanceof IUpdateOperator) {
	f2 = ((IUpdateOperator) f2.op()).target(f2);
	} 

	return f1.equalsModRenaming(f2);
    }

}
