package de.uka.ilkd.key.rule.label;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.logic.label.OriginTermLabel.SpecType;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.Rule;

/**
 * Refactoring for {@link OriginTermLabel}s.
 *
 * This ensures that {@link OriginTermLabel#getSubtermOrigins()}
 * always returns an up-to-date value.
 *
 * @author lanzinger
 */
public class OriginTermLabelRefactoring implements TermLabelRefactoring {

    @Override
    public ImmutableList<Name> getSupportedRuleNames() {
        return null;
    }

    @Override
    public RefactoringScope defineRefactoringScope(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm,
            Rule rule, Goal goal, Object hint, Term tacletTerm) {
        return RefactoringScope.APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE;
    }

    @Override
    public void refactorLabels(
            TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence,
            Term applicationTerm, Rule rule, Goal goal, Object hint, Term tacletTerm, Term term,
            List<TermLabel> labels) {

        if (rule instanceof BuiltInRule
                && !TermLabelRefactoring.shouldRefactorOnBuiltInRule(rule, goal, hint)) {
            return;
        }

        OriginTermLabel oldLabel = null;
        OriginTermLabel newLabel;

        Set<Origin> subtermOrigins = collectSubtermOrigins(term.subs(), new HashSet<>());

        for (TermLabel label : labels) {
            if (label instanceof OriginTermLabel) {
                oldLabel = (OriginTermLabel) label;
                break;
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

        if (OriginTermLabel.canAddLabel(term, services)
                && (!subtermOrigins.isEmpty() || newLabel.getOrigin().specType != SpecType.NONE)) {
            labels.add(newLabel);
        }
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
