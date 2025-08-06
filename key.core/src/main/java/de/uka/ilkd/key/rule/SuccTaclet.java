/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.rule.executor.javadl.SuccTacletExecutor;

import org.key_project.logic.ChoiceExpr;
import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.rules.TacletAnnotation;
import org.key_project.prover.rules.TacletApplPart;
import org.key_project.prover.rules.TacletAttributes;
import org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.prover.sequent.Sequent;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;

/**
 * A SuccTaclet represents a taclet whose find part has to match a top level formula in the
 * succedent of the sequent.
 */
public class SuccTaclet extends FindTaclet {
    /**
     * creates a {@link Taclet} (old name Schematic Theory Specific Rule) with the given parameters
     * that works on the succedent.
     *
     * @param name the name of the {@link Taclet}
     * @param applPart contains the application part of a taclet that is the if-sequent, the
     *        variable conditions
     * @param goalTemplates a list of goal descriptions.
     * @param heuristics a list of heuristics for the Taclet
     * @param attrs attributes for the Taclet; these are boolean values indicating a non-interactive
     *        or recursive use of the Taclet.
     * @param find the find sequent of the Taclet
     * @param prefixMap an ImmutableMap from {@link SchemaVariable} to {@link TacletPrefix} that
     *        contains
     *        the prefix for each SchemaVariable in the taclet
     */
    public SuccTaclet(Name name, TacletApplPart applPart,
            ImmutableList<TacletGoalTemplate> goalTemplates, ImmutableList<RuleSet> heuristics,
            TacletAttributes attrs, Sequent find,
            ImmutableMap<SchemaVariable, org.key_project.prover.rules.TacletPrefix> prefixMap,
            ChoiceExpr choices,
            ImmutableSet<TacletAnnotation> tacletAnnotations) {
        super(name, applPart, goalTemplates, heuristics, attrs, find, prefixMap, choices,
            tacletAnnotations);
    }

    @Override
    public JTerm find() {
        return (JTerm) ((Sequent) find).succedent().getFirst().formula();
    }

    @Override
    protected void createAndInitializeExecutor() {
        executor = new SuccTacletExecutor(this);
    }

    /** toString for the find part */
    protected StringBuffer toStringFind(StringBuffer sb) {
        return sb.append("\\find(==>").append(find().toString()).append(")\n");
    }

    @Override
    public @NonNull SuccTaclet setName(@NonNull String s) {
        final TacletApplPart applPart =
            new TacletApplPart(assumesSequent(), applicationRestriction(), varsNew(),
                varsNotFreeIn(),
                varsNewDependingOn(), getVariableConditions());
        final TacletAttributes attrs = new TacletAttributes(displayName(), trigger);
        return new SuccTaclet(new Name(s), applPart, goalTemplates(), getRuleSets(), attrs,
            (Sequent) find,
            prefixMap, choices, tacletAnnotations);
    }


}
