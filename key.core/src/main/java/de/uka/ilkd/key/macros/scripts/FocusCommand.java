/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.macros.scripts.meta.Description;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.Varargs;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.BuiltInRuleAppIndex;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Focuses on a given sequent by hiding all formulas that are not in the given parameter sequent.
 *
 * @author Mattias Ulbrich
 */
public class FocusCommand extends AbstractCommand<FocusCommand.Parameters> {

    private static final Name HIDELEFT_TACLET_NAME = new Name("hide_left");
    private static final Name HIDERIGHT_TACLET_NAME = new Name("hide_right");

    public FocusCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "focus";
    }

    @Override
    protected void execute(Parameters args) throws ScriptException, InterruptedException {
        Goal goal = state.getFirstOpenAutomaticGoal();
        final Sequent focusSequent = args.sequent;
        final Sequent sequent = goal.sequent();
        FindTaclet hideLeft = (FindTaclet) state.getProof().getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(HIDELEFT_TACLET_NAME);

        Collection<SequentFormula> toRemove = filter(focusSequent.antecedent(), sequent.antecedent(), goal.proof().getServices());
        for (SequentFormula sf : toRemove) {
            goal = removeFormula(sf, hideLeft, goal, true);
        }

        FindTaclet hideRight = (FindTaclet) state.getProof().getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(HIDERIGHT_TACLET_NAME);
        toRemove = filter(focusSequent.succedent(), sequent.succedent(), goal.proof().getServices());
        for (SequentFormula sf : toRemove) {
            goal = removeFormula(sf, hideRight, goal, false);
        }
    }

    private static Goal removeFormula(SequentFormula sf, FindTaclet hideRule, Goal goal, boolean isAntec) {
        Services services = goal.proof().getServices();
        PosInOccurrence pio = new PosInOccurrence(sf, PosInTerm.getTopLevel(), isAntec);
        SchemaVariable sv = hideRule.collectSchemaVars().iterator().next();
        SVInstantiations svi = SVInstantiations.EMPTY_SVINSTANTIATIONS.add(sv, sf.formula(), services);
        TacletApp app = PosTacletApp.createPosTacletApp(hideRule, svi, pio, services);
        ImmutableList<Goal> goals = goal.apply(app);
        assert goals.size() == 1;
        goal = goals.head();
        return goal;
    }

    private Collection<SequentFormula> filter(Semisequent match, Semisequent concrete, Services services) {
        List<SequentFormula> result = new ArrayList<>();
        TermComparisonWithHoles tc = new TermComparisonWithHoles(services);

        for (SequentFormula seqformula : concrete) {
            Term formula = seqformula.formula();
            boolean keep = false;
            for (SequentFormula matchFormula : match) {
                if (tc.compareModHoles(matchFormula.formula(), formula)) {
                    keep = true;
                    break;
                }
            }
            if(!keep) {
                result.add(seqformula);
            }
        }

        return result;
    }

    @Description("Focuses on a given sequent by hiding all formulas that are not in the given parameter sequent.")
    public static class Parameters {
        @Option(value = "#2", help = "The sequent to focus on. Matching mechanisms are supported.")
        Sequent sequent;
    }
}
