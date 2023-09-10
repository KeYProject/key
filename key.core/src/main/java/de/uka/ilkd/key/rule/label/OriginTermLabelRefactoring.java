/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.logic.label.OriginTermLabel.SpecType;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.FormulaTag;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

/**
 * Refactoring for {@link OriginTermLabel}s.
 *
 * This ensures that {@link OriginTermLabel#getSubtermOrigins()} always returns an up-to-date value.
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
        if (rule instanceof BuiltInRule
                && !TermLabelRefactoring.shouldRefactorOnBuiltInRule(rule, goal, hint)) {
            return RefactoringScope.NONE;
        } else if (rule instanceof Taclet && !shouldRefactorOnTaclet((Taclet) rule)) {
            return RefactoringScope.NONE;
        } else {
            return RefactoringScope.APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE;
        }
    }

    @Override
    public void refactorLabels(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm, Term term, List<TermLabel> labels) {
        if (services.getProof() == null) {
            return;
        }

        if (rule instanceof BuiltInRule
                && !TermLabelRefactoring.shouldRefactorOnBuiltInRule(rule, goal, hint)) {
            return;
        }

        if (rule instanceof Taclet && !shouldRefactorOnTaclet((Taclet) rule)) {
            return;
        }

        OriginTermLabel oldLabel = null;

        for (TermLabel label : labels) {
            if (label instanceof OriginTermLabel) {
                oldLabel = (OriginTermLabel) label;
                break;
            }
        }

        if (!ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings()
                .getUseOriginLabels()) {
            if (oldLabel != null) {
                labels.remove(oldLabel);
            }
            return;
        }

        Set<Origin> subtermOrigins = collectSubtermOrigins(term.subs(), new LinkedHashSet<>());

        OriginTermLabel newLabel = null;
        if (oldLabel != null) {
            labels.remove(oldLabel);
            final Origin oldOrigin = oldLabel.getOrigin();
            newLabel = new OriginTermLabel(oldOrigin, subtermOrigins);
        } else if (!subtermOrigins.isEmpty()) {
            final Origin commonOrigin = OriginTermLabel.computeCommonOrigin(subtermOrigins);
            newLabel = new OriginTermLabel(commonOrigin, subtermOrigins);
        }

        if (newLabel != null) {
            final Origin origin = newLabel.getOrigin();
            if (OriginTermLabel.canAddLabel(term, services)
                    && (!subtermOrigins.isEmpty() || origin.specType != SpecType.NONE)) {
                labels.add(newLabel);
            }
        }
    }

    private Set<Origin> collectSubtermOrigins(ImmutableArray<Term> terms, Set<Origin> result) {
        for (Term term : terms) {
            collectSubtermOrigins(term, result);
        }

        return result;
    }

    /**
     * Determines whether any refactorings should be applied on an application of the given taclet.
     * For some taclets, performing refactorings causes {@link FormulaTag}s to go missing.
     *
     * @param taclet a taclet rule.
     * @return whether any refactorings should be applied on an application of the given rule.
     *
     * @see TermLabelRefactoring#shouldRefactorOnBuiltInRule(Rule, Goal, Object)
     */
    private boolean shouldRefactorOnTaclet(Taclet taclet) {
        return !taclet.name().toString().startsWith("arrayLength")
                && taclet.goalTemplates().size() <= 1;
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
