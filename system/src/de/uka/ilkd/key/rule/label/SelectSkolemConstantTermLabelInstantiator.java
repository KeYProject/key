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
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.label.SelectSkolemConstantTermLabel;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Rule;


/**
 * The {@link ITermLabelWorker} used during prove to define how a
 * {@link AuxiliaryTermLabel} is maintained.
 * @author Christoph Scheben
 */
public final class SelectSkolemConstantTermLabelInstantiator implements ITermLabelWorker {

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
    public String getName() {
        return SelectSkolemConstantTermLabel.NAME.toString();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public List<ITermLabel> instantiateLabels(Term tacletTerm,
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
            tacletTerm.containsLabel(SelectSkolemConstantTermLabel.INSTANCE)) {
            // keep SelectSkolemConstantTermLabel
            return Collections.<ITermLabel>singletonList(SelectSkolemConstantTermLabel.INSTANCE);

        } else {
            // in all other cases the tacletTerm cannot contain the
            // SelectSkolemConstantTermLabel, because it is attached only
            // to constants
            return null;
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
                             List<ITermLabel> newLabels) {
        // since we'd like to keep the SelectSkolemConstantTermLabel, there is
        // nothing to do here
    }
}