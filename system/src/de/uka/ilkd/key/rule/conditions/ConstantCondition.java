// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * This variable condition checks if an instantiation is a constant formula or term,
 * i.e. its arity is equal to zero.
 *
 * @author Michael Kirsten
 */
public class ConstantCondition extends VariableConditionAdapter {

    private final AbstractSortedOperator t;
    private final boolean negated;

    public ConstantCondition(AbstractSortedOperator t, boolean negated) {
        this.t = t;
        this.negated = negated;
    }

    @Override
    public boolean check(SchemaVariable var,
                         SVSubstitute instCandidate,
                         SVInstantiations instMap,
                         Services services) {
        if ((!(var instanceof TermSV)
                    || var != this.t)
                && (!(var instanceof FormulaSV)
                        || var != this.t)) {
            return true;
        }
        if (var instanceof TermSV) {
            Term tInst = (Term) instMap.getInstantiation((TermSV)t);
            boolean atomic = (tInst.arity() == 0);
            return negated ? !atomic : atomic;
        }
        if (var instanceof FormulaSV) {
            Term tInst = (Term) instMap.getInstantiation((FormulaSV)t);
            boolean atomic = (tInst.arity() == 0);
            return negated ? !atomic : atomic;
        }
        return false;
    }

    @Override
    public String toString() {
        return (negated ? "\\not":"") + "\\isConstant (" + t + ")";
    }
}