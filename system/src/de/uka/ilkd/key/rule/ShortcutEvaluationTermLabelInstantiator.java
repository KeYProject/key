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

import java.util.Collections;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.ShortcutEvaluationTermLabel;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.TransformerFunction;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.label.ITermLabelWorker;

/**
 * The {@link ITermLabelWorker} used for variable conditions in taclets
 * to define how a {@link ShortcutEvaluationTermLabel} is maintained.
 * <p/>
 *
 * @author Michael Kirsten
 */
public class ShortcutEvaluationTermLabelInstantiator implements ITermLabelWorker {
    /**
     * The only instance of this class.
     */
    public static final ShortcutEvaluationTermLabelInstantiator INSTANCE =
            new ShortcutEvaluationTermLabelInstantiator();

    /**
     * Constructor to forbid multiple instances.
     */
    private ShortcutEvaluationTermLabelInstantiator() {
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
        if (tacletTerm != null // tacletTerm is a disjunction or conjunction
                && tacletTerm.arity() == 2
                && (tacletTerm.op().equals(Junctor.AND)
                        || tacletTerm.op().equals(Junctor.OR))
                && tacletTerm.containsLabel(ShortcutEvaluationTermLabel.INSTANCE)
                && TransformerFunction.inTransformer(applicationPosInOccurrence)) {
            final TransformerFunction t =
                    TransformerFunction.getTransformer(applicationPosInOccurrence);
            if (TransformerFunction.inTransformer(applicationPosInOccurrence)
                    && (t.name().equals(new Name("wd"))
                            || t.name().equals(new Name("WD")))) {
             // keep ShortcutEvaluationTermLabel
                return Collections.<ITermLabel>singletonList(ShortcutEvaluationTermLabel.INSTANCE);
            }
        }
        return null;
    }

    @Override
    public String getName() {
        return ShortcutEvaluationTermLabel.NAME.toString();
    }

    protected ITermLabel getTermLabel(Term applicationTerm) {
        return ShortcutEvaluationTermLabel.INSTANCE;
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
        // Keep label only in transformer functions "WD" and "wd"
        if (TransformerFunction.inTransformer(applicationPosInOccurrence)) {
            final TransformerFunction t =
                    TransformerFunction.getTransformer(applicationPosInOccurrence);
            if (t.name().equals(new Name("wd")) || t.name().equals(new Name("WD"))) {
                return;
            }
        }
        ITermLabel termLabel = getTermLabel(termToUpdate);
        if (termLabel != null) {
            newLabels.remove(termLabel);
        }
    }
}