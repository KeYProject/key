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
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.AuxiliaryTermLabel;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import java.util.LinkedList;
import java.util.List;


/**
 * The {@link ITermLabelWorker} used during prove to define how a
 * {@link AuxiliaryTermLabel} is maintained.
 * <p/>
 * @author Christoph Scheben
 */
public final class AuxiliaryTermLabelInstantiator implements ITermLabelWorker {

    /**
     * The only instance of this class.
     */
    public static final AuxiliaryTermLabelInstantiator INSTANCE =
            new AuxiliaryTermLabelInstantiator();

    /**
     * Constructor to forbid multiple instances.
     */
    private AuxiliaryTermLabelInstantiator() {
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getName() {
        return AuxiliaryTermLabel.NAME.toString();
    }


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
        // nothing to do
        return new LinkedList<ITermLabel>();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public List<ITermLabel> updateLabels(Term tacletTerm,
                                         PosInOccurrence applicationPosInOccurrence,
                                         Term termToUpdate,
                                         Rule rule,
                                         Goal goal) {
        // keep labels
        List<ITermLabel> updatedLabels = new LinkedList<ITermLabel>();
        if (termToUpdate.containsLabel(AuxiliaryTermLabel.INSTANCE)) {
            updatedLabels.add(AuxiliaryTermLabel.INSTANCE);
        }
        return updatedLabels;
    }
}