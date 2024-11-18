/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.prover.rules.TacletApplPart;
import org.key_project.rusty.rule.executor.rustydl.AntecTacletExecutor;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

/**
 * An AntecTaclet represents a taclet whose find part has to match a top level formula in the
 * antecedent of the sequent.
 */
public class AntecTaclet extends FindTaclet {
    private final boolean ignoreTopLevelUpdates;

    /**
     * creates a Schematic Theory Specific Rule (Taclet) with the given parameters.
     *
     * @param name the name of the Taclet
     * @param applPart contains the application part of a Taclet that is the if-sequent, the
     *        variable conditions
     * @param goalTemplates a list of goal descriptions.
     * @param attrs attributes for the Taclet; these are boolean values indicating a non-interactive
     *        or recursive use of the Taclet.
     * @param find the find term of the Taclet
     * @param prefixMap a ImmutableMap that contains the prefix for each
     *        SchemaVariable in the Taclet
     */
    public AntecTaclet(Name name, TacletApplPart applPart,
            ImmutableList<? extends org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate> goalTemplates,
            org.key_project.prover.rules.TacletAttributes attrs, Term find,
            boolean ignoreTopLevelUpdates,
            ImmutableMap<org.key_project.logic.op.sv.SchemaVariable, org.key_project.prover.rules.TacletPrefix> prefixMap,
            ImmutableSet<org.key_project.prover.rules.TacletAnnotation> tacletAnnotations) {
        super(name, applPart, goalTemplates, attrs, find, prefixMap,
            tacletAnnotations);
        this.ignoreTopLevelUpdates = ignoreTopLevelUpdates;
        createTacletServices();
    }

    /**
     * this method is used to determine if top level updates are allowed to be ignored. This may be
     * the case if we have an Antec or SuccTaclet but not for a RewriteTaclet
     *
     * @return true if top level updates shall be ignored
     */
    @Override
    public boolean ignoreTopLevelUpdates() {
        return ignoreTopLevelUpdates;
    }


    /** toString for the find part */
    @Override
    protected StringBuffer toStringFind(StringBuffer sb) {
        return sb.append("\\find(").append(find().toString()).append("==>)\n");
    }

    @Override
    protected void createAndInitializeExecutor() {
        executor = new AntecTacletExecutor<>(this);
    }

    @Override
    public AntecTaclet setName(String s) {
        final TacletApplPart applPart =
            new TacletApplPart(assumesSequent(), varsNew(), varsNotFreeIn(),
                varsNewDependingOn(), getVariableConditions());
        final org.key_project.prover.rules.TacletAttributes attrs =
            new org.key_project.prover.rules.TacletAttributes(displayName(), null);

        return new AntecTaclet(new Name(s), applPart, goalTemplates(), attrs, find,
            ignoreTopLevelUpdates, prefixMap, tacletAnnotations);
    }
}
