/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.rule.executor.javadl.NoFindTacletExecutor;

import org.key_project.logic.ChoiceExpr;
import org.key_project.logic.Name;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.*;
import org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;

/**
 * Used to implement a Taclet that has no <I>find</I> part. This kind of taclet is not attached to
 * term or formula, but to a complete sequent. A typical representant is the <code>cut</code> rule.
 */
public class NoFindTaclet extends Taclet {

    /**
     * creates a {@link Taclet} (previously Schematic Theory Specific Rule) with the given
     * parameters.
     *
     * @param name the name of the Taclet
     * @param applPart contains the application part of a Taclet that is the if-sequent, the
     *        variable conditions
     * @param goalTemplates the IList containing all goal descriptions of the
     *        taclet to be created
     * @param ruleSets a list of rule sets for the Taclet
     * @param attrs attributes for the Taclet; these are boolean values
     * @param prefixMap a ImmutableMap that contains the prefix for each
     *        SchemaVariable in the Taclet
     * @param choices the SetOf<Choices> to which this taclet belongs to
     */
    public NoFindTaclet(Name name, TacletApplPart applPart,
            ImmutableList<TacletGoalTemplate> goalTemplates, ImmutableList<RuleSet> ruleSets,
            TacletAttributes attrs,
            ImmutableMap<SchemaVariable, org.key_project.prover.rules.TacletPrefix> prefixMap,
            ChoiceExpr choices, ImmutableSet<TacletAnnotation> tacletAnnotations) {
        super(name, null, applPart, goalTemplates, ruleSets, attrs, prefixMap, choices,
            tacletAnnotations);
    }

    @Override
    protected void createAndInitializeExecutor() {
        executor = new NoFindTacletExecutor(this);
    }

    /**
     * @return Set of schemavariables of the if and the (optional) find part
     */
    @Override
    public ImmutableSet<SchemaVariable> getAssumesAndFindVariables() {
        return getAssumesVariables();
    }

    /**
     * the empty set as a no find taclet has no other entities where variables cann occur bound than
     * in the goal templates
     *
     * @return empty set
     */
    @Override
    protected ImmutableSet<QuantifiableVariable> getBoundVariablesHelper() {
        return DefaultImmutableSet.nil();
    }

    @Override
    public @NonNull NoFindTaclet setName(@NonNull String s) {
        final TacletApplPart applPart =
            new TacletApplPart(assumesSequent(), applicationRestriction(), varsNew(),
                varsNotFreeIn(),
                varsNewDependingOn(), getVariableConditions());
        final TacletAttributes attrs = new TacletAttributes(displayName(), trigger);

        return new NoFindTaclet(new Name(s), applPart, goalTemplates(), getRuleSets(), attrs,
            prefixMap, choices, tacletAnnotations);
    }

}
