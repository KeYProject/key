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
package de.uka.ilkd.key.rule.label;

import java.util.Collections;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelUtil;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Rule;


/**
 * The {@link TermLabelInstantiator} used during prove to define how a
 * {@link AuxiliaryTermLabel} is maintained.
 * @author Christoph Scheben
 */
public final class SelectSkolemConstantTermLabelInstantiator implements TermLabelInstantiator {

    /**
     * The only instance of this class.
     */
    public static final SelectSkolemConstantTermLabelInstantiator INSTANCE =
            new SelectSkolemConstantTermLabelInstantiator();

    /**
     * Constructor to forbid multiple instances.
     */
    private SelectSkolemConstantTermLabelInstantiator() {
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public List<TermLabel> instantiateLabels(Term tacletTerm,
                                              PosInOccurrence applicationPosInOccurrence,
                                              Term applicationTerm,
                                              Rule rule,
                                              Goal goal,
                                              Operator newTermOp,
                                              ImmutableArray<Term> newTermSubs,
                                              ImmutableArray<QuantifiableVariable> newTermBoundVars,
                                              JavaBlock newTermJavaBlock) {
        if (tacletTerm != null &&
            tacletTerm.arity() == 0 && // tacletTerm is a constant
            tacletTerm.containsLabel(TermLabelUtil.SELECT_SKOLEM_LABEL)) {
            // keep SelectSkolemConstantTermLabel
            return Collections.<TermLabel>singletonList(TermLabelUtil.SELECT_SKOLEM_LABEL);

        } else {
            // in all other cases the tacletTerm cannot contain the
            // SelectSkolemConstantTermLabel, because it is attached only
            // to constants
            return Collections.emptyList();
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void updateLabels(Term tacletTerm,
                             PosInOccurrence applicationPosInOccurrence,
                             Term termToUpdate,
                             Rule rule,
                             Goal goal,
                             List<TermLabel> newLabels) {
        // since we'd like to keep the SelectSkolemConstantTermLabel, there is
        // nothing to do here
    }
}