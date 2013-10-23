package de.uka.ilkd.key.rule.label;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Rule;

// not thread safe!!

public class CompositeTermLabelInstantiator implements TermLabelInstantiator {

    private final List<TermLabelInstantiator> instantiatorList = 
            new ArrayList<TermLabelInstantiator>();

    @Override 
    public List<TermLabel> instantiateLabels(Term tacletTerm,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Operator newTermOp, ImmutableArray<Term> newTermSubs,
            ImmutableArray<QuantifiableVariable> newTermBoundVars, JavaBlock newTermJavaBlock) {

        List<TermLabel> result = new LinkedList<TermLabel>();

        for (TermLabelInstantiator instantiator : instantiatorList) {
            List<TermLabel> labels = instantiator.instantiateLabels(tacletTerm,
                    applicationPosInOccurrence,
                    applicationPosInOccurrence != null ? applicationPosInOccurrence.subTerm()
                            : null, rule, goal, newTermOp, newTermSubs, newTermBoundVars,
                    newTermJavaBlock);
            assert labels != null : "Instantiators must not return null";
            result.addAll(labels);
        }

        return result;
    }

    @Override 
    public void updateLabels(Term tacletTerm, PosInOccurrence applicationPosInOccurrence,
            Term termToUpdate, Rule rule, Goal goal, List<TermLabel> newLabels) {
        for (TermLabelInstantiator instantiator : instantiatorList) {
            instantiator.updateLabels(tacletTerm, applicationPosInOccurrence, termToUpdate, rule,
                    goal, newLabels);
        }
    }

    public List<TermLabelInstantiator> getInstantiatorList() {
        return instantiatorList;
    }
}
