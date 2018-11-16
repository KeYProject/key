package de.uka.ilkd.key.rule.label;

import java.util.HashSet;
import java.util.Set;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;

public class OriginTermLabelUpdate implements TermLabelUpdate {

    @Override
    public ImmutableList<Name> getSupportedRuleNames() {
        return null;
    }

    @Override
    public void updateLabels(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Term modalityTerm,
            Rule rule, RuleApp ruleApp, Goal goal, Object hint, Term tacletTerm, Operator newTermOp,
            ImmutableArray<Term> newTermSubs, ImmutableArray<QuantifiableVariable> newTermBoundVars,
            JavaBlock newTermJavaBlock, Set<TermLabel> labels) {
        OriginTermLabel oldLabel = null;
        OriginTermLabel newLabel;

        Set<Origin> subtermOrigins = collectSubtermOrigins(newTermSubs, new HashSet<>());

        for (TermLabel label : labels) {
            if (label instanceof OriginTermLabel) {
                if (oldLabel != null) {
                    assert false;
                }

                oldLabel = (OriginTermLabel) label;
            }
        }

        if (oldLabel != null) {
            labels.remove(oldLabel);
            newLabel = new OriginTermLabel(
                    oldLabel.getOrigin().specType,
                    oldLabel.getOrigin().fileName,
                    oldLabel.getOrigin().line,
                    subtermOrigins);
        } else {
            newLabel = new OriginTermLabel(subtermOrigins);
        }

        labels.add(newLabel);
    }

    private Set<Origin> collectSubtermOrigins(ImmutableArray<Term> terms,
            HashSet<Origin> result) {
        for (Term term : terms) {
            collectSubtermOrigins(term, result);
        }

        return result;
    }

    @SuppressWarnings("unchecked")
    private Set<Origin> collectSubtermOrigins(Term term, Set<Origin> result) {
        TermLabel label = term.getLabel(OriginTermLabel.NAME);

        if (label != null) {
            result.add((Origin) label.getChild(0));
            result.addAll((Set<Origin>) label.getChild(1));
        }

        ImmutableArray<Term> subterms = term.subs();

        for (int i = 0; i < subterms.size(); ++i) {
            Term subterm = subterms.get(i);
            collectSubtermOrigins(subterm, result);
        }

        return result;
    }
}
