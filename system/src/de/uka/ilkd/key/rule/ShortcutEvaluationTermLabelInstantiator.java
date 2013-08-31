package de.uka.ilkd.key.rule;

import java.util.Collections;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.ShortcutEvaluationTermLabel;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.label.ITermLabelWorker;


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
                && tacletTerm.containsLabel(ShortcutEvaluationTermLabel.INSTANCE)) {
                // keep ShortcutEvaluationTermLabel
            return Collections.<ITermLabel>singletonList(ShortcutEvaluationTermLabel.INSTANCE);
        } else {
            return null;
        }
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
       // Remove label from branches of BuiltInRules except in Well-Definedness branches
       if (rule instanceof BuiltInRule &&
           !goal.node().getNodeInfo().getBranchLabel().startsWith("Well-Definedness")) {
          ITermLabel termLabel = getTermLabel(termToUpdate);
          if (termLabel != null) {
             newLabels.remove(termLabel);
          }
       }
    }
}