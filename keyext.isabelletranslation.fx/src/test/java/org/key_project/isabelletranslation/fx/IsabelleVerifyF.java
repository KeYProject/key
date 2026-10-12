/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.isabelletranslation.fx;

import java.lang.reflect.Method;
import java.time.Duration;
import java.time.Instant;
import java.util.List;
import javafx.stage.Stage;
import javafx.stage.Window;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.isabelletranslation.IsabelleTranslationSettings;
import org.key_project.isabelletranslation.automation.IsabelleLauncher;
import org.key_project.isabelletranslation.automation.IsabelleProblem;
import org.key_project.isabelletranslation.automation.IsabelleResult;
import org.key_project.isabelletranslation.automation.IsabelleSolver;
import org.key_project.util.javafx.FxUtil;

import org.jspecify.annotations.NullUnmarked;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Headless verify harness for the Isabelle solver-launch port ({@code key.fx.verify.isabelle},
 * forwarded by key.ui.fx/build.gradle and invoked reflectively by {@code MainWindowF}): a
 * <b>DRY-RUN</b> self test that exercises the {@link IsabelleLauncherProgressDialogMediatorF} +
 * {@link IsabelleSolverProgressDialogF} progress dialog with fake solvers — the dialog renders,
 * progress/status updates are applied, the Stop button cancels (the stop event reaches the
 * launcher), the DONE mode switches to Discard/Apply and the Info window renders — <b>without any
 * real Isabelle installation</b>: {@code IsabelleLauncher.launch} is never called and the scala
 * isabelle backend ({@code de.unruh.isabelle.*}) stays unloaded, which is asserted before and
 * after the run.
 * <p>
 * The harness must be called on the JavaFX thread after a demo proof has been loaded (the fake
 * solver problems need a real {@link Goal}).
 */
public final class IsabelleVerifyF {

    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleVerifyF.class);

    /** The scala-isabelle backend entry classes that must never load during the DRY-RUN. */
    private static final List<String> BACKEND_CLASSES = List.of(
        "de.unruh.isabelle.control.Isabelle",
        "de.unruh.isabelle.java.JIsabelle",
        "de.unruh.isabelle.pure.Theory");

    private IsabelleVerifyF() {
    }

    /**
     * Runs the DRY-RUN self test.
     *
     * @param owner the owner window for the dialogs
     * @param proof the loaded demo proof (a fake solver problem is built from its first goal)
     * @return the one-line report ending in {@code PASS} or {@code FAIL}
     */
    public static String run(Window owner, Proof proof) {
        if (proof == null) {
            return "Isabelle verify DRY-RUN: SKIP (no proof loaded)";
        }
        try {
            String backendBefore = backendState();
            if (!backendBefore.equals("UNLOADED")) {
                return "Isabelle verify DRY-RUN: FAIL (backend already loaded: " + backendBefore
                    + ")";
            }

            IsabelleTranslationSettings settings = IsabelleTranslationSettings.getInstance();
            Goal goal = proof.openGoals().stream().findFirst().orElse(null);
            if (goal == null) {
                return "Isabelle verify DRY-RUN: SKIP (no open goal in the demo proof)";
            }
            IsabelleProblem problem =
                new IsabelleProblem(goal, "theory VerifyDryRun", "theory VerifyDryRun begin end");

            StubSolver solver0 = new StubSolver(0, problem, 100);
            StubSolver solver1 = new StubSolver(1, problem, 100);
            StubLauncher launcher = new StubLauncher(settings);
            IsabelleLauncherProgressDialogMediatorF mediator =
                new IsabelleLauncherProgressDialogMediatorF(owner, proof, launcher);

            // launcherStarted: the progress dialog renders with one row per solver
            mediator.launcherStarted(launcher, List.of(solver0, solver1));
            IsabelleSolverProgressDialogF dialog = dialogOf(mediator);
            check(dialog != null, "dialog created");
            check(dialog.isShowing(), "dialog showing");
            check(dialog.rowCount() == 2, "dialog has 2 solver rows");

            // running solver: progress bar + remaining time text
            solver0.beginRun(Instant.now().minusSeconds(1));
            mediator.refreshDialog();
            check(textOf(dialog, 0).endsWith("sec."), "running status text ('" + textOf(dialog, 0)
                + "')");

            // stopped successfully: green "Valid (1.5s)"
            solver0.stop(IsabelleResult.getSuccessResult("simp", Duration.ofMillis(1500)));
            mediator.refreshDialog();
            check(textOf(dialog, 0).startsWith("Valid ("), "success status text ('"
                + textOf(dialog, 0) + "')");

            // cancellation: the Stop button event must reach the launcher (stopAll)
            mediator.stopEvent();
            check(launcher.stopped, "stop event reached the launcher (stopAll)");

            // interrupted by the user stop, then the launcher stops: DONE mode
            solver1.stop(IsabelleResult.getInterruptedResult());
            mediator.launcherStopped(launcher, List.of(solver0, solver1));
            check(dialog.modus() == IsabelleSolverProgressDialogF.Modus.SOLVERS_DONE,
                "modus SOLVERS_DONE after launcherStopped");
            check("Discard".equals(dialog.stopButtonText()), "stop button became Discard ('"
                + dialog.stopButtonText() + "')");
            check(dialog.isApplyEnabled(), "apply button enabled in DONE mode");
            check(overallTextOf(mediator).contains("Processed 2 of 2 problems."),
                "overall progress text");

            // info window: the theory + raw solver output tab dialog renders
            int windowsBefore = Window.getWindows().size();
            mediator.info(0);
            Stage infoStage = findInfoStage(windowsBefore);
            check(infoStage != null, "info window opened");
            if (infoStage != null) {
                check(infoStage.getTitle().startsWith("Information for "),
                    "info window title ('" + infoStage.getTitle() + "')");
                FxUtil.runLater(infoStage::close);
            }

            // discard: the dialog closes
            mediator.discardEvent();
            check(!dialog.isShowing(), "dialog closed after discardEvent");

            String backendAfter = backendState();
            check(backendAfter.equals("UNLOADED"),
                "scala-isabelle backend stayed unloaded (launch() never ran)");
            LOGGER.info("Isabelle verify DRY-RUN: dialog rendered, progress/status updates OK, "
                + "Stop cancellation OK, DONE mode OK, info window OK, backend {}", backendAfter);
            return "Isabelle verify DRY-RUN: dialog renders + cancellation works without the "
                + "Isabelle backend (" + backendAfter + ") PASS";
        } catch (RuntimeException | AssertionError e) {
            LOGGER.error("Isabelle verify DRY-RUN failed", e);
            return "Isabelle verify DRY-RUN: FAIL (" + e + ")";
        }
    }

    // --- seams on the mediator (package-private) ------------------------------------------------

    private static IsabelleSolverProgressDialogF dialogOf(
            IsabelleLauncherProgressDialogMediatorF mediator) {
        return mediator.dialog();
    }

    private static String textOf(IsabelleSolverProgressDialogF dialog, int row) {
        return dialog.rowText(row);
    }

    private static String overallTextOf(IsabelleLauncherProgressDialogMediatorF mediator) {
        return mediator.overallText();
    }

    // --- helpers --------------------------------------------------------------------------------

    private static void check(boolean condition, String what) {
        if (!condition) {
            throw new AssertionError("Isabelle verify DRY-RUN: " + what + " — failed");
        }
    }

    /** Whether the scala-isabelle backend classes are loaded on this class loader. */
    private static String backendState() {
        ClassLoader loader = IsabelleVerifyF.class.getClassLoader();
        for (String name : BACKEND_CLASSES) {
            if (isLoaded(loader, name)) {
                return "LOADED(" + name + ")";
            }
        }
        return "UNLOADED";
    }

    /**
     * Whether the class is already loaded on the given loader, <b>without loading it</b> —
     * {@code Class.forName(..., false, loader)} would itself load the class and thus always
     * report it present (the jar is on the classpath). Uses the protected
     * {@code ClassLoader.findLoadedClass} via reflection, which needs
     * {@code --add-opens java.base/java.lang=ALL-UNNAMED} (set for the run task in
     * key.ui.fx/build.gradle). Returns {@code null} when not loaded.
     */
    private static boolean isLoaded(ClassLoader loader, String name) {
        try {
            Method findLoadedClass =
                ClassLoader.class.getDeclaredMethod("findLoadedClass", String.class);
            findLoadedClass.setAccessible(true);
            return findLoadedClass.invoke(loader, name) != null;
        } catch (ReflectiveOperationException | RuntimeException e) {
            throw new IllegalStateException(
                "cannot check the loaded state of " + name + " without loading it "
                    + "(--add-opens java.base/java.lang=ALL-UNNAMED missing?): " + e,
                e);
        }
    }

    private static Stage findInfoStage(int windowsBefore) {
        for (Window window : Window.getWindows()) {
            if (window instanceof Stage stage && stage.getTitle() != null
                    && stage.getTitle().startsWith("Information for ")) {
                return stage;
            }
        }
        LOGGER.warn("Isabelle verify DRY-RUN: no info stage found among {} windows (before: {})",
            Window.getWindows().size(), windowsBefore);
        return null;
    }

    /**
     * Launcher stub for the DRY-RUN: only {@link #stopAll()} is exercised (the verify never calls
     * {@code launch}, which would boot the real Isabelle backend).
     */
    private static final class StubLauncher extends IsabelleLauncher {
        boolean stopped;

        StubLauncher(IsabelleTranslationSettings settings) {
            super(settings);
        }

        @Override
        public void stopAll() {
            stopped = true;
        }
    }

    /**
     * Solver stub implementing the {@link IsabelleSolver} interface with plain Java only —
     * loading it never touches the scala-isabelle classes.
     */
    @NullUnmarked
    private static final class StubSolver implements IsabelleSolver {
        private final int index;
        private final IsabelleProblem problem;
        private final int timeout;
        private SolverState state = SolverState.Waiting;
        private IsabelleResult result;
        private Instant startTime = Instant.now();
        private Duration computationTime = Duration.ZERO;

        StubSolver(int index, IsabelleProblem problem, int timeout) {
            this.index = index;
            this.problem = problem;
            this.timeout = timeout;
        }

        void beginRun(Instant start) {
            this.startTime = start;
            this.state = SolverState.Running;
        }

        void stop(IsabelleResult result) {
            this.result = result;
            this.state = SolverState.Stopped;
            if (result.getType() == IsabelleResult.Type.SUCCESS) {
                this.computationTime = result.getComputationTime();
            }
        }

        @Override
        public int getSolverIndex() {
            return index;
        }

        @Override
        public String name() {
            return "IsabelleSledgehammer";
        }

        @Override
        public IsabelleProblem getProblem() {
            return problem;
        }

        @Override
        public Throwable getException() {
            return result != null ? result.getException() : null;
        }

        @Override
        public void abort() {
            state = SolverState.Stopped;
        }

        @Override
        public Instant getStartTime() {
            return startTime;
        }

        @Override
        public Duration getComputationTime() {
            return computationTime;
        }

        @Override
        public int getTimeout() {
            return timeout;
        }

        @Override
        public void setTimeout(int timeout) {
            // not exercised by the DRY-RUN
        }

        @Override
        public SolverState getState() {
            return state;
        }

        @Override
        public String getRawSolverOutput() {
            return "dry-run solver output";
        }

        @Override
        public String getRawSolverInput() {
            return "theory VerifyDryRun begin end";
        }

        @Override
        public IsabelleResult getFinalResult() {
            return result;
        }

        @Override
        public IsabelleResult call() {
            return result;
        }
    }
}
