/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.List;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.scripts.meta.Argument;
import de.uka.ilkd.key.scripts.meta.Documentation;

import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;

/**
 * The command object CutCommand has as scriptcommand name "cut" As parameters: a formula with the
 * id "#2"
 */
public class CutCommand extends AbstractCommand {
    private static final Name CUT_TACLET_NAME = new Name("cut");

    public CutCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "cut";
    }

    // From within JML scripts, "assert" is more common than "cut"
    @Override
    public List<String> getAliases() {
        return List.of(getName(), "assert");
    }

    @Override
    public void execute(ScriptCommandAst arguments) throws ScriptException, InterruptedException {
        var args = state().getValueInjector().inject(new Parameters(), arguments);
        execute(state(), args);
    }

    static void execute(EngineState state, Parameters args) throws ScriptException {
        Taclet cut = state.getProof().getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(CUT_TACLET_NAME);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();

        var formula =
            state.getProof().getServices().getTermBuilder().convertToFormula(args.formula);

        app = app.addCheckedInstantiation(sv, formula, state.getProof().getServices(), true);
        state.getFirstOpenAutomaticGoal().apply(app);
    }

    @Documentation(category = "Fundamental", value = """
            The cut command makes a case distinction (a cut) on a formula on the current proof goal.
            From within JML scripts, the alias 'assert' is more common than using 'cut'.
            If followed by a `\\by proof` suffix in JML, it refers the sequent where
            the cut formula is introduced to the succedent (i.e. where it is to be established).
            """)
    public static class Parameters {
        @Argument
        @Documentation("The formula to make the case distinction on.")
        public @MonotonicNonNull JTerm formula;
    }

}
