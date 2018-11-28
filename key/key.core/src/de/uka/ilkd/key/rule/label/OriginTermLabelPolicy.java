package de.uka.ilkd.key.rule.label;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.logic.label.OriginTermLabel.SpecType;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Rule;;

/**
 * Policy for {@link OriginTermLabel}s.
 * 
 * This ensures that every term always has a valid term label, i.e., that no labels are lost.
 * 
 * @author lanzinger
 */
public class OriginTermLabelPolicy implements TermLabelPolicy {

    @Override
    public TermLabel keepLabel(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm, Operator newTermOp, ImmutableArray<Term> newTermSubs,
            ImmutableArray<QuantifiableVariable> newTermBoundVars, JavaBlock newTermJavaBlock,
            ImmutableArray<TermLabel> newTermOriginalLabels, TermLabel label) {
        if (!TermLabelRefactoring.shouldRefactorOnBuiltInRule(rule, goal, hint)) {
            return label;
        }
        
        OriginTermLabel newLabel = (OriginTermLabel) label;
        OriginTermLabel oldLabel = null;

        for (TermLabel l : newTermOriginalLabels) {
            if (l instanceof OriginTermLabel && l != newLabel) {
                oldLabel = (OriginTermLabel) l;
                break;
            }
        }

        OriginTermLabel result;

        if (oldLabel == null) {
            result = newLabel;
        } else {
            result = oldLabel;
        }

        //TODO This is probably not correct, but it prevents the origin being lost in some cases
        // (like for OneStepSimplification).
        if (result.getSubtermOrigins().size() == 1
                && result.getOrigin().specType == SpecType.NONE) {
            Origin origin = result.getSubtermOrigins().iterator().next();

            result = new OriginTermLabel(origin.specType, origin.fileName, origin.line,
                    result.getSubtermOrigins());
        }

        return result;
    }
}
