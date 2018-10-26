package de.uka.ilkd.key.rule.label;

import java.util.LinkedList;
import java.util.List;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Rule;

/**
 * Refactoring used for {@link OriginTermLabel}s.
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
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm) {
        return RefactoringScope.APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE_AND_PARENTS;
    }

    @Override
    public void refactorLabels(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm, Term term, List<TermLabel> labels) {
        List<OriginTermLabel> originLabels = new LinkedList<>();

        for (TermLabel label : labels) {
            if (label instanceof OriginTermLabel) {
                originLabels.add((OriginTermLabel) label);
            }
        }

        if (originLabels.size() > 1) {
            labels.removeAll(originLabels);
            labels.add(new OriginTermLabel(originLabels));
        }
    }

}
