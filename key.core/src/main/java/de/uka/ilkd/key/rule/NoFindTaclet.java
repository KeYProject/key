/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.ChoiceExpr;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.executor.javadl.NoFindTacletExecutor;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

/**
 * Used to implement a Taclet that has no <I>find</I> part. This kind of taclet is not attached to
 * term or formula, but to a complete sequent. A typical representant is the <code>cut</code> rule.
 */
public class NoFindTaclet extends Taclet {

    /**
     * creates a Schematic Theory Specific Rule (Taclet) with the given parameters.
     *
     * @param name the name of the Taclet
     * @param applPart contains the application part of an Taclet that is the if-sequent, the
     *        variable conditions
     * @param goalTemplates the IList<TacletGoalTemplate> containg all goal descriptions of the
     *        taclet to be created
     * @param ruleSets a list of rule sets for the Taclet
     * @param attrs attributes for the Taclet; these are boolean values
     * @param prefixMap a ImmMap<SchemaVariable,TacletPrefix> that contains the prefix for each
     *        SchemaVariable in the Taclet
     * @param choices the SetOf<Choices> to which this taclet belongs to
     */
    public NoFindTaclet(Name name, TacletApplPart applPart,
            ImmutableList<TacletGoalTemplate> goalTemplates, ImmutableList<RuleSet> ruleSets,
            TacletAttributes attrs, ImmutableMap<SchemaVariable, TacletPrefix> prefixMap,
            ChoiceExpr choices, ImmutableSet<TacletAnnotation> tacletAnnotations) {
        super(name, applPart, goalTemplates, ruleSets, attrs, prefixMap, choices,
            tacletAnnotations);
        createTacletServices();
    }

    @Override
    protected void createAndInitializeExecutor() {
        executor = new NoFindTacletExecutor(this);
    }

    /**
     * @return Set of schemavariables of the if and the (optional) find part
     */
    @Override
    public ImmutableSet<SchemaVariable> getIfFindVariables() {
        return getIfVariables();
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
    public NoFindTaclet setName(String s) {
        final TacletApplPart applPart = new TacletApplPart(ifSequent(), varsNew(), varsNotFreeIn(),
            varsNewDependingOn(), getVariableConditions());
        final TacletAttributes attrs = new TacletAttributes();
        attrs.setDisplayName(displayName());

        return new NoFindTaclet(new Name(s), applPart, goalTemplates(), getRuleSets(), attrs,
            prefixMap, choices, tacletAnnotations);
    }


}
