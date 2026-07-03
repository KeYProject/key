/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.StrictTermKey;
import de.uka.ilkd.key.logic.label.LabelCollection;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.logic.label.OriginTermLabel.SpecType;
import de.uka.ilkd.key.logic.label.OriginTermLabelFactory;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelContext;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.Taclet;

import org.key_project.logic.Name;
import org.key_project.prover.indexing.FormulaTag;
import org.key_project.prover.rules.Rule;
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
    public RefactoringScope defineRefactoringScope(TermLabelContext context) {
        if (context.rule() instanceof BuiltInRule
                && !TermLabelRefactoring.shouldRefactorOnBuiltInRule(context.rule(), context.goal(),
                    context.hint())) {
            return RefactoringScope.NONE;
        } else if (context.rule() instanceof Taclet
                && !shouldRefactorOnTaclet((Taclet) context.rule())) {
            return RefactoringScope.NONE;
        } else {
            return RefactoringScope.APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE;
        }
    }

    @Override
    public void refactorLabels(TermLabelContext context, JTerm term, LabelCollection labels) {
        if (context.services().getProof() == null) {
            return;
        }

        if (context.rule() instanceof BuiltInRule
                && !TermLabelRefactoring.shouldRefactorOnBuiltInRule(context.rule(), context.goal(),
                    context.hint())) {
            return;
        }

        if (context.rule() instanceof Taclet && !shouldRefactorOnTaclet((Taclet) context.rule())) {
            return;
        }

        final OriginTermLabel oldLabel = labels.getFirst(OriginTermLabel.class);

        if (context.services().getTermBuilder().getOriginFactory() == null) {
            if (oldLabel != null) {
                labels.remove(oldLabel);
            }
            return;
        }

        // cache origins per term to avoid a quadratic recursive collection per rule
        // application
        final Map<StrictTermKey, Set<Origin>> originsCache =
            context.services().getCaches().getSubtermOriginsCache();
        Set<Origin> subtermOrigins = new LinkedHashSet<>();
        for (JTerm sub : term.subs()) {
            subtermOrigins.addAll(collectSubtermOrigins(sub, originsCache));
        }
        OriginTermLabelFactory factory = context.services().getTermBuilder().getOriginFactory();
        OriginTermLabel newLabel = null;
        if (oldLabel != null) {
            labels.remove(oldLabel);
            final Origin oldOrigin = oldLabel.getOrigin();
            newLabel = factory.createOriginTermLabel(oldOrigin, subtermOrigins);
        } else if (!subtermOrigins.isEmpty()) {
            final Origin commonOrigin = OriginTermLabel.computeCommonOrigin(subtermOrigins);

            newLabel = factory.createOriginTermLabel(commonOrigin, subtermOrigins);
        }

        if (newLabel != null) {
            final Origin origin = newLabel.getOrigin();
            if (OriginTermLabel.canAddLabel(term, context.services())
                    && (!subtermOrigins.isEmpty() || origin.specType != SpecType.NONE)) {
                labels.add(newLabel);
            }
        }
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

    /**
     * @param term a term
     * @param originsCache memoization of the result per term, see
     *        {@link de.uka.ilkd.key.java.ServiceCaches#getSubtermOriginsCache()}
     * @return the origins of {@code term} (including its own label) and of all its
     *         subterms; the returned set is unmodifiable and shared, do not mutate
     */
    @SuppressWarnings("unchecked")
    private Set<Origin> collectSubtermOrigins(JTerm term,
            Map<StrictTermKey, Set<Origin>> originsCache) {
        // origins live in term labels: a label-free subtree cannot contribute any
        if (!term.containsLabelsRecursive()) {
            return Collections.emptySet();
        }

        // the cache key must be label-sensitive as the value is derived from the labels
        final StrictTermKey key = new StrictTermKey(term);
        Set<Origin> cached = originsCache.get(key);
        if (cached != null) {
            return cached;
        }

        Set<Origin> result = new LinkedHashSet<>();
        TermLabel label = term.getLabel(OriginTermLabel.NAME);

        if (label != null) {
            result.add((Origin) label.getTLChild(0));
            result.addAll((Set<Origin>) label.getTLChild(1));
        }

        ImmutableArray<JTerm> subterms = term.subs();
        for (int i = 0; i < subterms.size(); ++i) {
            result.addAll(collectSubtermOrigins(subterms.get(i), originsCache));
        }

        Set<Origin> stored =
            result.isEmpty() ? Collections.emptySet() : Collections.unmodifiableSet(result);
        originsCache.put(key, stored);
        return stored;
    }

}
