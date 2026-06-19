/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;


import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.scripts.meta.Argument;

import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.Term;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;

import static de.uka.ilkd.key.logic.equality.TermLabelsProperty.TERM_LABELS_PROPERTY;

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
public class HideCommand extends AbstractCommand {

    private static final Name HIDE_LEFT = new Name("hide_left");
    private static final Name HIDE_RIGHT = new Name("hide_right");

    public HideCommand() {
        super(Parameters.class);
    }


    @Override
    public void execute(ScriptCommandAst arguments) throws ScriptException, InterruptedException {
        var args = state().getValueInjector().inject(new Parameters(), arguments);

        Goal goal = state().getFirstOpenAutomaticGoal();

        Taclet hideLeft =
            state().getProof().getEnv().getInitConfigForEnvironment().lookupActiveTaclet(HIDE_LEFT);
        for (SequentFormula s : args.sequent.antecedent()) {
            TacletApp app = NoPosTacletApp.createNoPosTacletApp(hideLeft);
            SequentFormula s2 = find(s, goal.sequent().antecedent());
            SchemaVariable sv = app.uninstantiatedVars().iterator().next();
            app = app.addCheckedInstantiation(sv, (JTerm) s2.formula(),
                service, true);
            app = app.setPosInOccurrence(new PosInOccurrence(s2, PosInTerm.getTopLevel(), true),
                service);
            goal.apply(app);
        }

        Taclet hideRight =
            state().getProof().getEnv().getInitConfigForEnvironment()
                    .lookupActiveTaclet(HIDE_RIGHT);
        for (SequentFormula s : args.sequent.succedent()) {
            TacletApp app = NoPosTacletApp.createNoPosTacletApp(hideRight);
            SequentFormula s2 = find(s, goal.sequent().succedent());
            SchemaVariable sv = app.uninstantiatedVars().iterator().next();
            app = app.addCheckedInstantiation(sv, (JTerm) s2.formula(),
                service, true);
            app = app.setPosInOccurrence(new PosInOccurrence(s2, PosInTerm.getTopLevel(), false),
                service);
            goal.apply(app);
        }
    }

    private SequentFormula find(
            SequentFormula sf, Semisequent semiseq)
            throws ScriptException {
        for (SequentFormula s : semiseq) {
            Term term = s.formula();
            Term formula = sf.formula();
            if ((TERM_LABELS_PROPERTY).equalsModThisProperty(term, formula)) {
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
        @Argument
        @MonotonicNonNull
        public Sequent sequent;
    }

}
