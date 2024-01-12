/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.util.collection.ImmutableList;

/**
 * The command "focus" allows you to select formulas from the current sequent
 * to focus verification on. This means that all other formulas are discarded
 * (i.e. hidden using hide_right, hide_left).
 *
 * Benefits are: The automation is guided into focussing on a relevant set of
 * formulas.
 *
 * The selected set of sequent formulas can be regarded as an equivalent to an
 * unsat core.
 *
 * @author Created by sarah on 1/12/17.
 * @author Mattias Ulbrich, 2023
 */
public class FocusCommand extends AbstractCommand<FocusCommand.Parameters> {

    public FocusCommand() {
        super(Parameters.class);
    }

    static class Parameters {
        @Option("#2")
        public Sequent toKeep;
    }

    @Override
    public void execute(Parameters s) throws ScriptException, InterruptedException {
        if (s == null) {
            throw new ScriptException("Missing 'sequent' argument for focus");
        }

        Sequent toKeep = s.toKeep;

        hideAll(toKeep);
    }

    @Override
    public String getName() {
        return "focus";
    }

    /**
     * Hide all formulas of the sequent that are not on focus sequent
     *
     * @param toKeep sequent containing formulas to keep
     * @throws ScriptException if no goal is currently open
     */
    private void hideAll(Sequent toKeep) throws ScriptException {
        Goal goal = state.getFirstOpenAutomaticGoal();
        assert goal != null : "not null by contract of the method";

        // The formulas to keep in the antecedent
        ImmutableList<Term> keepAnte = toKeep.antecedent().asList().map(SequentFormula::formula);
        ImmutableList<SequentFormula> ante = goal.sequent().antecedent().asList();

        for (SequentFormula seqFormula : ante) {
            // This means "!keepAnte.contains(seqFormula.formula)" but with equality mod renaming!
            if (!keepAnte.exists(it -> it.equalsModRenaming(seqFormula.formula()))) {
                Taclet tac = getHideTaclet("left");
                makeTacletApp(goal, seqFormula, tac, true);
            }
        }

        ImmutableList<Term> keepSucc = toKeep.succedent().asList().map(SequentFormula::formula);
        ImmutableList<SequentFormula> succ = goal.sequent().succedent().asList();
        for (SequentFormula seqFormula : succ) {
            if (!keepSucc.exists(it -> it.equalsModRenaming(seqFormula.formula()))) {
                Taclet tac = getHideTaclet("right");
                makeTacletApp(goal, seqFormula, tac, false);
            }
        }
    }

    // determine where formula in sequent and apply either hide_left or hide_right
    private Taclet getHideTaclet(String pos) {
        String ruleName = "hide_" + pos;
        return proof.getEnv().getInitConfigForEnvironment().lookupActiveTaclet(new Name(ruleName));
    }

    /**
     * Make tacletApp for one sequent formula to hide on the sequent
     *
     * @param g the goal on which this hide rule should be applied to
     * @param toHide the sequent formula to hide
     * @param tac the taclet top apply (either hide_left or hide_right)
     * @param antec whether the formula is in the antecedent
     */
    private void makeTacletApp(Goal g, SequentFormula toHide, Taclet tac, boolean antec) {

        // hide rules only applicable to top-level terms/sequent formulas
        PosInTerm pit = PosInTerm.getTopLevel();

        PosInOccurrence pio = new PosInOccurrence(toHide, pit, antec);

        Set<SchemaVariable> svs = tac.collectSchemaVars();
        assert svs.size() == 1;
        Iterator<SchemaVariable> iter = svs.iterator();
        SchemaVariable sv = iter.next();

        SVInstantiations inst = SVInstantiations.EMPTY_SVINSTANTIATIONS;

        TacletApp app =
            PosTacletApp.createPosTacletApp((FindTaclet) tac, inst, pio, proof.getServices());
        app = app.addCheckedInstantiation(sv, toHide.formula(), proof.getServices(), true);
        g.apply(app);

    }

}
