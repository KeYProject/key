/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.*;

import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.ValueInjector;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class SMTCommand extends AbstractCommand<SMTCommand.SMTCommandArguments> {
    private static final Logger LOGGER = LoggerFactory.getLogger(SMTCommand.class);

    private static final Map<String, SolverType> SOLVER_MAP = computeSolverMap();

    public SMTCommand() {
        super(SMTCommandArguments.class);
    }

    private static Map<String, SolverType> computeSolverMap() {
        Map<String, SolverType> result = new HashMap<>();

        for (SolverType type : SolverTypes.getSolverTypes()) {
            result.put(type.getName(), type);
        }

        return Collections.unmodifiableMap(result);
    }

    @Override
    public SMTCommandArguments evaluateArguments(EngineState state, Map<String, String> arguments)
            throws Exception {
        return ValueInjector.injection(this, new SMTCommandArguments(), arguments);
    }

    @Override
    public String getName() {
        return "smt";
    }

    @Override
    public void execute(SMTCommandArguments args) throws ScriptException, InterruptedException {
        SolverTypeCollection su = computeSolvers(args.solver);

        ImmutableList<Goal> goals;
        if (args.all) {
            goals = state.getProof().openGoals();
        } else {
            goals = ImmutableSLList.<Goal>nil().prepend(state.getFirstOpenAutomaticGoal());
        }

        for (Goal goal : goals) {
            runSMT(args, su, goal);
        }
    }

    private void runSMT(SMTCommandArguments args, SolverTypeCollection su, Goal goal) {
        DefaultSMTSettings settings =
            new DefaultSMTSettings(goal.proof().getSettings().getSMTSettings(),
                ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(),
                goal.proof().getSettings().getNewSMTSettings(), goal.proof());

        if (args.timeout >= 0) {
            settings = new SMTSettingsTimeoutWrapper(settings, args.timeout);
        }

        SolverLauncher launcher = new SolverLauncher(settings);
        Collection<SMTProblem> probList = new LinkedList<>();
        probList.add(new SMTProblem(goal));
        TimerListener timerListener = new TimerListener();
        launcher.addListener(timerListener);
        launcher.launch(su.getTypes(), probList, goal.proof().getServices());

        for (SMTProblem problem : probList) {
            SMTSolverResult finalResult = problem.getFinalResult();
            if (finalResult.isValid() == ThreeValuedTruth.VALID) {
                IBuiltInRuleApp app = SMTRuleApp.RULE.createApp(args.solver);
                app = app.tryToInstantiate(problem.getGoal());
                problem.getGoal().apply(app);
            }
            LOGGER.info("Finished run on goal " + goal.node().serialNr() + " in "
                + timerListener.getRuntime() + "ms, result is " + finalResult);
        }
    }

    private SolverTypeCollection computeSolvers(String value) throws ScriptException {
        String[] parts = value.split(" *, *");
        List<SolverType> types = new ArrayList<>();
        for (String name : parts) {
            SolverType type = SOLVER_MAP.get(name);
            if (type == null) {
                throw new ScriptException("Unknown SMT solver: " + name);
            }
            types.add(type);
        }
        return new SolverTypeCollection(value, 1, types);
    }

    public static class SMTCommandArguments {
        @Option("solver")
        public String solver = "Z3";

        @Option(value = "all", required = false)
        public boolean all = false;

        @Option(value = "timeout", required = false)
        public int timeout = -1;
    }

    private static class TimerListener implements SolverLauncherListener {
        private long start;
        private long stop;

        @Override
        public void launcherStarted(Collection<SMTProblem> problems,
                Collection<SolverType> solverTypes, SolverLauncher launcher) {
            this.start = System.currentTimeMillis();
        }

        @Override
        public void launcherStopped(SolverLauncher launcher,
                Collection<SMTSolver> finishedSolvers) {
            this.stop = System.currentTimeMillis();
        }

        public long getRuntime() {
            return stop - start;
        }
    }

    private static class SMTSettingsTimeoutWrapper extends DefaultSMTSettings {
        private final int timeout;

        public SMTSettingsTimeoutWrapper(DefaultSMTSettings settings, int timeout) {
            super(settings.getPdSettings(), settings.getPiSettings(),
                settings.getNewTranslationSettings(), settings.getProof());
            this.timeout = timeout;
        }

        @Override
        public long getTimeout() {
            return timeout;
        }
    }
}
