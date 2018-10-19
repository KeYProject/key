package de.uka.ilkd.key.rule.label;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Rule;

/**
 * This policy adds every label of every (direct or indirect) child of the application term to the
 * new term.
 *
 * @author lanzinger
 */
public class PerpetualChildTermLabelPolicy implements ChildTermLabelPolicy {

    @Override
    public ImmutableList<Name> getSupportedRuleNames() {
        return null;
    }

    @Override
    public boolean isRuleApplicationSupported(TermServices services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm, Operator newTermOp, ImmutableArray<Term> newTermSubs,
            ImmutableArray<QuantifiableVariable> newTermBoundVars, JavaBlock newTermJavaBlock) {
        return true;
    }

    @Override
    public boolean addLabel(TermServices services, PosInOccurrence applicationPosInOccurrence,
            Term applicationTerm, Rule rule, Goal goal, Object hint, Term tacletTerm,
            Operator newTermOp, ImmutableArray<Term> newTermSubs,
            ImmutableArray<QuantifiableVariable> newTermBoundVars, JavaBlock newTermJavaBlock,
            Term childTerm, TermLabel label) {
        return true;
    }

}
