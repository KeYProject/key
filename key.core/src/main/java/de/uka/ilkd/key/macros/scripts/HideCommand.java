/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Proof script command to hide a formula from the sequent.
 *
 * Usage:
 *
 * <pre>
 *     hide "f1, f2 ==> f3, f4"
 * </pre>
 *
 * All formulas in the parameter sequent are hidden using hide_left or using hide_right.
 *
 * @author Mattias Ulbrich
 */
public class HideCommand extends AbstractCommand<HideCommand.Parameters> {

    private static final Name HIDE_LEFT = new Name("hide_left");
    private static final Name HIDE_RIGHT = new Name("hide_right");

    public HideCommand() {
        super(Parameters.class);
    }

    @Override
    public Parameters evaluateArguments(EngineState state, Map<String, String> arguments)
            throws Exception {
        return state.getValueInjector().inject(this, new Parameters(), arguments);
    }

    @Override
    public void execute(Parameters args) throws ScriptException, InterruptedException {

        Goal goal = state.getFirstOpenAutomaticGoal();

        Taclet hideLeft =
            state.getProof().getEnv().getInitConfigForEnvironment().lookupActiveTaclet(HIDE_LEFT);
        for (SequentFormula s : args.sequent.antecedent()) {
            TacletApp app = NoPosTacletApp.createNoPosTacletApp(hideLeft);
            SequentFormula s2 = find(s, goal.sequent().antecedent());
            SchemaVariable sv = app.uninstantiatedVars().iterator().next();
            app = app.addCheckedInstantiation(sv, s2.formula(), service, true);
            app = app.setPosInOccurrence(new PosInOccurrence(s2, PosInTerm.getTopLevel(), true),
                service);
            goal.apply(app);
        }

        Taclet hideRight =
            state.getProof().getEnv().getInitConfigForEnvironment().lookupActiveTaclet(HIDE_RIGHT);
        for (SequentFormula s : args.sequent.succedent()) {
            TacletApp app = NoPosTacletApp.createNoPosTacletApp(hideRight);
            SequentFormula s2 = find(s, goal.sequent().succedent());
            SchemaVariable sv = app.uninstantiatedVars().iterator().next();
            app = app.addCheckedInstantiation(sv, s2.formula(), service, true);
            app = app.setPosInOccurrence(new PosInOccurrence(s2, PosInTerm.getTopLevel(), false),
                service);
            goal.apply(app);
        }
    }

    private SequentFormula find(SequentFormula sf, Semisequent semiseq) throws ScriptException {
        for (SequentFormula s : semiseq) {
            if (s.formula().equalsModTermLabels(sf.formula())) {
                return s;
            }
        }
        throw new ScriptException("This formula is not on the sequent: " + sf);
    }

    @Override
    public String getName() {
        return "hide";
    }

    public static class Parameters {
        @Option("#2")
        public Sequent sequent;
    }

}
