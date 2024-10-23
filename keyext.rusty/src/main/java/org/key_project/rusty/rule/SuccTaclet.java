/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.ncore.rules.TacletAnnotation;
import org.key_project.ncore.rules.TacletApplPart;
import org.key_project.ncore.rules.TacletAttributes;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.rule.executor.rustydl.SuccTacletExecutor;
import org.key_project.rusty.rule.tacletbuilder.TacletGoalTemplate;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

/**
 * A SuccTaclet represents a taclet whose find part has to match a top level formula in the
 * succedent of the sequent.
 */
public class SuccTaclet extends FindTaclet {
    private final boolean ignoreTopLevelUpdates;

    /**
     * creates a {@link Taclet} (old name Schematic Theory Specific Rule) with the given parameters
     * that works on the succedent.
     *
     * @param name the name of the {@link Taclet}
     * @param applPart contains the application part of a taclet that is the if-sequent, the
     *        variable conditions
     * @param goalTemplates a list of goal descriptions.
     * @param attrs attributes for the Taclet; these are boolean values indicating a non-interactive
     *        or recursive use of the Taclet.
     * @param find the find term of the Taclet
     * @param prefixMap an ImmutableMap from {@link SchemaVariable} to {@link TacletPrefix} that
     *        contains
     *        the prefix for each SchemaVariable in the taclet
     */
    public SuccTaclet(Name name, TacletApplPart applPart,
            ImmutableList<TacletGoalTemplate> goalTemplates,
            TacletAttributes attrs, Term find, boolean ignoreTopLevelUpdates,
            ImmutableMap<org.key_project.logic.op.sv.SchemaVariable, org.key_project.ncore.rules.TacletPrefix> prefixMap,
            ImmutableSet<TacletAnnotation> tacletAnnotations) {
        super(name, applPart, goalTemplates, attrs, find, prefixMap,
            tacletAnnotations);
        this.ignoreTopLevelUpdates = ignoreTopLevelUpdates;
        createTacletServices();
    }

    @Override
    protected void createAndInitializeExecutor() {
        executor = new SuccTacletExecutor<>(this);
    }

    /**
     * this method is used to determine if top level updates are allowed to be ignored. This is the
     * case if we have an Antec or SuccTaclet but not for a RewriteTaclet
     *
     * @return true if top level updates shall be ignored
     */
    @Override
    public boolean ignoreTopLevelUpdates() {
        return ignoreTopLevelUpdates;
    }



    /** toString for the find part */
    protected StringBuffer toStringFind(StringBuffer sb) {
        return sb.append("\\find(==>").append(find().toString()).append(")\n");
    }

    @Override
    public SuccTaclet setName(String s) {
        final TacletApplPart applPart =
            new TacletApplPart(assumesSequent(), varsNew(), varsNotFreeIn(),
                varsNewDependingOn(), getVariableConditions());
        final TacletAttributes attrs = new TacletAttributes(displayName(), null);

        return new SuccTaclet(new Name(s), applPart,
            (ImmutableList<TacletGoalTemplate>) goalTemplates(), attrs, find,
            ignoreTopLevelUpdates, prefixMap, tacletAnnotations);
    }

}
