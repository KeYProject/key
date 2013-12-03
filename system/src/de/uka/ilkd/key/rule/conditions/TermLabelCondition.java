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

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.TermLabelSV;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * This variable condition checks if an instantiation for term labels contains a specific
 * term label.
 *
 * @author Michael Kirsten
 */
public class TermLabelCondition extends VariableConditionAdapter {

    private final TermLabelSV l;
    private final Name ln;
    private final boolean negated;

    public TermLabelCondition(TermLabelSV l, String t, boolean negated) {
        this.l = l;
        this.ln = new Name(t);
        this.negated = negated;
    }

    @Override
    public boolean check(SchemaVariable var, SVSubstitute instCandidate,
                         SVInstantiations instMap, Services services) {
        assert instMap.getInstantiation(l) instanceof ImmutableArray<?>;
        ImmutableArray<?> tInsts = (ImmutableArray<?>) instMap.getInstantiation(l);
        boolean hasLabel = hasLabel(tInsts, ln);
        return negated ? !hasLabel : hasLabel;
    }

    /**
     * Checks if an array of label contains the label specified in this condition
     * @param labels array of labels in the term to be matched
     * @param name name of the label specified in this condition
     * @return true if label matches, false if not
     */
    static boolean hasLabel(ImmutableArray<?> labels, Name name) {
        boolean found = false;
        for (Object o: labels) {
            assert o instanceof TermLabel;
            TermLabel label = (TermLabel)o;
            found = found || (label.name().compareTo(name) == 0);
        }
        return found;
    }

    @Override
    public String toString() {
        return (negated ? "\\not":"") + "\\hasLabel (" + l + ", " + ln + ")";
    }
}