/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.logic.ChoiceExpr;
import org.key_project.logic.Name;
import org.key_project.prover.rules.ApplicationRestriction;
import org.key_project.prover.rules.TacletApplPart;
import org.key_project.prover.rules.TacletAttributes;
import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

public class CheatCommand extends NoArgumentCommand {
    private static final Taclet CHEAT_TACLET;

    static {
        TacletApplPart applPart =
            new TacletApplPart(JavaDLSequentKit.getInstance().getEmptySequent(),
                ApplicationRestriction.NONE, ImmutableList.of(), ImmutableList.of(),
                ImmutableList.of(), ImmutableList.of());
        CHEAT_TACLET =
            new NoFindTaclet(new Name("CHEAT"), applPart, ImmutableList.of(), ImmutableList.of(),
                new TacletAttributes("cheat", null), DefaultImmutableMap.nilMap(), ChoiceExpr.TRUE,
                ImmutableSet.empty());
    }

    @Override
    public String getName() {
        return "cheat";
    }

    @Override
    public String getDocumentation() {
        return "Use this to close a goal unconditionally. This is unsound and should only " +
            "be used for testing and proof debugging purposes. It is similar to 'sorry' " +
            "in Isabelle or 'admit' in Rocq.";
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, ScriptCommandAst ast,
            EngineState state)
            throws ScriptException, InterruptedException {
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(CHEAT_TACLET);
        state.getFirstOpenAutomaticGoal().apply(app);
    }
}
