package de.uka.ilkd.key.gui.smt;

import de.uka.ilkd.key.gui.smt.SolverListener.InternSMTProblem;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;

/// Compute unsat core from SMT problems and hide all irrelevant formulas from sequent.
/// Temporary hack to evaluate the potential of such a technique

public class SMTFocusResults {
    public static void focus(Collection<InternSMTProblem> smtProblems, Services services) {

        for (InternSMTProblem problem : smtProblems) {

            SMTSolver solver = problem.solver;

            if (solver.getFinalResult().isValid() != ThreeValuedTruth.VALID) {
                continue;
            }

            System.out.println(">>> " + solver.getRawSolverOutput());

            String[] lines = solver.getRawSolverOutput().split("\n");
            String lastLine = lines[lines.length - 1];

            assert lastLine.matches("(.*)");

            lastLine = lastLine.substring(1, lastLine.length() - 1);

            String[] labels = lastLine.trim().split(" +");
            Integer[] numbers = new Integer[labels.length];
            for (int i = 0; i < numbers.length; i++) {
                numbers[i] = Integer.parseInt(labels[i].substring(2));
            }

            Goal goal = problem.getProblem().getGoal();

            List<TacletApp> taclets = goal.getAllTacletApps(services);

            FindTaclet hideLeft = (FindTaclet)goal.proof().getEnv().getInitConfigForEnvironment()
                    .lookupActiveTaclet(new Name("hide_left"));

            FindTaclet hideRight = (FindTaclet)goal.proof().getEnv().getInitConfigForEnvironment()
                    .lookupActiveTaclet(new Name("hide_right"));

            HashSet<Integer> unsatCore = new HashSet<>(Arrays.asList(numbers));

            Semisequent antecedent = goal.node().sequent().antecedent();
            int i = 0;
            for (SequentFormula sf : antecedent) {
                if (!unsatCore.contains(i)) {
                    // TODO: ugly way of acessing. Can be done better?!
                    SchemaVariable schema = hideLeft.collectSchemaVars().iterator().next();
                    TacletApp app = PosTacletApp.createPosTacletApp(hideLeft, new MatchConditions(),
                            new PosInOccurrence(sf, PosInTerm.getTopLevel(), true),
                            services);
                    app = app.addCheckedInstantiation(schema, sf.formula(), services, true);
                    goal = goal.apply(app).iterator().next();
                }
                i++;
            }

            Semisequent succedent = goal.node().sequent().succedent();
            for (SequentFormula sf : succedent) {
                if (!unsatCore.contains(i)) {
                    // TODO: ugly way of acessing. Can be done better?!
                    SchemaVariable schema = hideRight.collectSchemaVars().iterator().next();
                    TacletApp app = PosTacletApp.createPosTacletApp(hideRight, new MatchConditions(),
                            new PosInOccurrence(sf, PosInTerm.getTopLevel(), false),
                            services);
                    app = app.addCheckedInstantiation(schema, sf.formula(), services, true);
                    goal = goal.apply(app).iterator().next();
                }
                i++;
            }

        }

    }
}
