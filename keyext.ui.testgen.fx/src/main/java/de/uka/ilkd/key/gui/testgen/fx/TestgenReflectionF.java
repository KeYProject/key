/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.testgen.fx;

import java.lang.reflect.Array;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Proxy;
import java.util.Collection;
import java.util.List;
import java.util.concurrent.atomic.AtomicReference;
import javafx.stage.Stage;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The reflective bridge to the {@code key.core} / {@code key.core.testgen} generation logic.
 * <p>
 * <b>NOT part of the SPI:</b> neither key.core nor key.core.testgen is on the compile classpath
 * of this module (the frozen {@code build.gradle} only exposes {@code key.ui.fx} and the Swing
 * {@code keyext.ui.testgen}; the core modules arrive on the runtime classpath of the app), so all
 * calls into the proof tree, the SMT machinery and the test-case generators are dispatched through
 * plain reflection. The routed entry points mirror the ones the Swing extension uses:
 * <ul>
 * <li>{@link #generateTestcases(Object, Object, LogSinkF)} — the headless CLI pipeline
 * {@code TestgenFacade.generateTestcases} (TestgenFacade.java:43-101): bounded symbolic
 * execution (FinishSymbolicExecution / TestGen macro), semantic blasting and the Z3 CE run with
 * JUnit test-suite generation. The Swing {@code TGWorker} drives the same steps through
 * {@code AbstractTestGenerator} (which needs a UI subclass that cannot be materialised without the
 * compile-time types); the facade is its headless counterpart that works off a plain
 * {@code KeYEnvironment}.</li>
 * <li>{@link #searchCounterExample(Object, Object, Object, LogSinkF, AtomicReference)} — the
 * counterexample search of {@code AbstractSideProofCounterExampleGenerator.searchCounterExample}
 * (side proof creation via {@code SideProofUtil}, {@code SemanticsBlastingMacro} on the side
 * proof, then Z3 CE via a {@code SolverLauncher}). The abstract generator's
 * {@code createSolverListener} hook is UI-specific; this port passes a reflective
 * {@code SolverLauncherListener} instead and reports the outcome into the {@link LogSinkF}.</li>
 * </ul>
 * Every reflective call is guarded: a missing class or a reflection error is logged through the
 * {@link LogSinkF} (and the module logger) instead of crashing the FX thread; a propagated
 * {@code InterruptedException} is re-thrown so the {@code Task} of the run dialogs turns into the
 * "cancelled" state (the FX equivalent of the Swing interruption handling).
 */
@NullMarked
final class TestgenReflectionF {

    private static final Logger LOGGER = LoggerFactory.getLogger(TestgenReflectionF.class);

    /**
     * the {@code Choice} activating the "ban runtime exceptions" taclet option of the side proof.
     */
    private static final String[] BAN_RUNTIME_EXCEPTIONS = { "ban", "runtimeExceptions" };

    private TestgenReflectionF() {
    }

    // ------------------------------------------------------------------ window/mediator access

    /**
     * {@code window.getUserInterfaceControl()} — the UserInterfaceControl of the FX window. The
     * window is passed as a plain {@code Object}: every {@code MainWindowF} type use in this
     * module forces javac to complete the class file, which fails ("Cannot attach type
     * annotations ... to MainWindowF.lastEnvironment: class file for
     * de.uka.ilkd.key.control.KeYEnvironment not found").
     */
    static @Nullable Object uiOf(@Nullable Object window) {
        return callNullary(window, "getUserInterfaceControl");
    }

    /** {@code window.getMediator()} — the FX mediator of the window. */
    static @Nullable Object mediatorOf(@Nullable Object window) {
        return callNullary(window, "getMediator");
    }

    /** {@code window.getStage()} — the stage the FX window is bound to. */
    static @Nullable Stage stageOf(@Nullable Object window) {
        return callNullary(window, "getStage") instanceof Stage stage ? stage : null;
    }

    /** {@code mediator.getSelectedProof()} — the currently selected proof or {@code null}. */
    static @Nullable Object proofOf(@Nullable Object mediator) {
        return callNullary(mediator, "getSelectedProof");
    }

    /** {@code mediator.getSelectedNode()} — the currently selected node or {@code null}. */
    static @Nullable Object nodeOf(@Nullable Object mediator) {
        return callNullary(mediator, "getSelectedNode");
    }

    /** {@code mediator.getSelectedGoal()} — the currently selected goal or {@code null}. */
    static @Nullable Object goalOf(@Nullable Object mediator) {
        return callNullary(mediator, "getSelectedGoal");
    }

    /** {@code mediator.autoModeRunningProperty()} — the observable auto-mode state. */
    static @Nullable Object autoModePropertyOf(@Nullable Object mediator) {
        return callNullary(mediator, "autoModeRunningProperty");
    }

    /** {@code goal.proof()} of a reflected {@code Goal}. */
    static @Nullable Object proofOfGoal(Object goal) {
        return callNullary(goal, "proof");
    }

    /** {@code goal.sequent()} of a reflected {@code Goal}. */
    static @Nullable Object sequentOfGoal(Object goal) {
        return callNullary(goal, "sequent");
    }

    // ------------------------------------------------------------------ enablement helpers

    /**
     * Whether the Z3 CE solver is installed (Swing TestGenerationAction.checkZ3CE,
     * TestGenerationAction.java:101-111: {@code SolverTypes.Z3_CE_SOLVER.isInstalled(false)}).
     */
    static boolean z3CeInstalled() {
        try {
            Object z3 = Class.forName("de.uka.ilkd.key.smt.solvertypes.SolverTypes")
                    .getField("Z3_CE_SOLVER").get(null);
            return (Boolean) z3.getClass().getMethod("isInstalled", boolean.class).invoke(z3,
                false);
        } catch (ReflectiveOperationException | RuntimeException e) {
            LOGGER.warn("Could not query the Z3 CE solver installation state", e);
            return false;
        }
    }

    /**
     * Whether the reflected node is an open leaf (Swing CounterExampleAction.selectedNodeChanged,
     * CounterExampleAction.java:67-79: {@code node.childrenCount() == 0 && !node.isClosed()}).
     */
    static boolean isOpenLeaf(@Nullable Object node) {
        if (node == null) {
            return false;
        }
        try {
            int children = (Integer) node.getClass().getMethod("childrenCount").invoke(node);
            boolean closed = (Boolean) node.getClass().getMethod("isClosed").invoke(node);
            return children == 0 && !closed;
        } catch (ReflectiveOperationException | RuntimeException e) {
            LOGGER.warn("Could not inspect the selected node", e);
            return false;
        }
    }

    // ------------------------------------------------------------------ test-case generation

    /**
     * Runs the test-case generation (Swing TGWorker.doInBackground, TGWorker.java:50-53). The
     * routed pipeline is {@code TestgenFacade.generateTestcases}: bounded symbolic execution,
     * testing with the TestGen macro, semantic blasting of the test data constraints and the
     * final Z3 CE run that writes the JUnit test suite into the configured output folder
     * (TestgenFacade.java:43-101).
     * <p>
     * <b>KNOWN-SIMPLIFIED:</b> the Swing {@code TGWorker} additionally wraps the run in the
     * mediator's auto-mode machinery and supports an immediate stop through the
     * {@code StopRequest}/{@code SolverLauncher} handles (TGWorker.java:42-71); the facade route
     * has no launcher handle, so stopping the FX run interrupts the worker thread, which the
     * macros honour between phases (the Z3 launch itself runs until it returns).
     *
     * @param ui the UserInterfaceControl of the main window (reflected)
     * @param proof the selected proof (reflected)
     * @param sink the log sink of the run dialog
     * @throws InterruptedException when the run was interrupted (task cancelled)
     */
    static void generateTestcases(Object ui, Object proof, LogSinkF sink)
            throws InterruptedException {
        if (ui == null || proof == null) {
            sink.writeln("Test generation cancelled: no proof loaded.");
            return;
        }
        try {
            Class<?> settingsClass = clazz("de.uka.ilkd.key.testgen.TestGenerationSettings");
            Object settings = settingsClass.getMethod("getInstance").invoke(null);
            Class<?> uiClass = clazz("de.uka.ilkd.key.control.UserInterfaceControl");
            Class<?> initConfigClass = clazz("de.uka.ilkd.key.proof.init.InitConfig");
            Class<?> proofClass = clazz("de.uka.ilkd.key.proof.Proof");
            Class<?> envClass = clazz("de.uka.ilkd.key.control.KeYEnvironment");
            Class<?> listenerClass =
                clazz("de.uka.ilkd.key.testgen.smt.testgen.TestGenerationLifecycleListener");

            Object initConfig = invokeNullary(proof, "getInitConfig");
            Object env = envClass.getConstructor(uiClass, initConfigClass).newInstance(ui,
                initConfig);
            Object listener = lifecycleListenerProxy(listenerClass, sink);
            Class<?> facade = clazz("de.uka.ilkd.key.testgen.TestgenFacade");
            Method generate = facade.getMethod("generateTestcases", envClass, proofClass,
                settingsClass, listenerClass);
            generate.invoke(null, env, proof, settings, listener);
        } catch (InvocationTargetException e) {
            Throwable cause = e.getCause();
            if (cause instanceof InterruptedException ie) {
                Thread.currentThread().interrupt();
                throw ie;
            }
            sink.error(cause == null ? e : cause);
        } catch (ReflectiveOperationException | RuntimeException e) {
            sink.error(e);
        }
    }

    // ------------------------------------------------------------------ counterexample search

    /**
     * Searches a counterexample for the sequent of the selected goal (Swing
     * {@code CounterExampleAction.CEWorker.doInBackground},
     * CounterExampleAction.java:175-181). The steps mirror
     * {@code AbstractSideProofCounterExampleGenerator}: create a hidden side proof from the goal's
     * sequent ({@code SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier} with the
     * "ban runtime exceptions" choice + {@code createSideProof}), run the
     * {@code SemanticsBlastingMacro} on it and launch the Z3 CE solver (the same pipeline as
     * {@code AbstractCounterExampleGenerator.searchCounterExample},
     * AbstractCounterExampleGenerator.java:67-100).
     * <p>
     * <b>KNOWN-SIMPLIFIED:</b> the Swing {@code SolverListener} opens a modal progress dialog and
     * a results dialog showing the counterexample model; the FX port prints the SMT statistics
     * (solved/invalid/unknown path conditions) and the found/not-found outcome into the run
     * dialog's log and leaves the model inspection to the generated test data. The auto-mode
     * shell of the Swing worker (CounterExampleAction.java:169-191) is dropped like in
     * {@link TestGenerationTaskF}.
     *
     * @param ui the UserInterfaceControl of the main window (reflected)
     * @param proof the proof of the selected goal (reflected)
     * @param sequent the sequent of the selected goal (reflected)
     * @param sink the log sink of the run dialog
     * @param launcherRef receives the running {@code SolverLauncher} so the Stop button can ask it
     *        to stop
     * @throws InterruptedException when the run was interrupted (task cancelled)
     */
    static void searchCounterExample(Object ui, Object proof, Object sequent, LogSinkF sink,
            AtomicReference<@Nullable Object> launcherRef) throws InterruptedException {
        if (ui == null || proof == null || sequent == null) {
            sink.writeln("Counterexample search cancelled: no goal selected.");
            return;
        }
        if (!z3CeInstalled()) {
            sink.writeln("Could not find the z3 SMT solver. Aborting.");
            return;
        }
        try {
            Class<?> proofClass = clazz("de.uka.ilkd.key.proof.Proof");
            Class<?> sequentClass = clazz("org.key_project.prover.sequent.Sequent");
            Class<?> choiceClass = clazz("org.key_project.logic.Choice");
            Class<?> sideProofUtil = clazz("de.uka.ilkd.key.util.SideProofUtil");
            Class<?> proofEnvClass = clazz("de.uka.ilkd.key.proof.mgt.ProofEnvironment");

            String proofName = "Semantics Blasting: " + invokeNullary(proof, "name");

            // (1) side proof, as AbstractSideProofCounterExampleGenerator.createProof
            // (AbstractSideProofCounterExampleGenerator.java:30-44)
            Object[] choices =
                (Object[]) Array.newInstance(choiceClass, BAN_RUNTIME_EXCEPTIONS.length);
            for (int i = 0; i < BAN_RUNTIME_EXCEPTIONS.length; i++) {
                choices[i] = choiceClass.getConstructor(String.class, String.class)
                        .newInstance(BAN_RUNTIME_EXCEPTIONS[i], "runtimeExceptions");
            }
            Method cloneEnv = sideProofUtil.getMethod(
                "cloneProofEnvironmentWithOwnOneStepSimplifier", proofClass,
                choiceClass.arrayType());
            Object env = cloneEnv.invoke(null, proof, choices);
            Object starter = sideProofUtil.getMethod("createSideProof", proofEnvClass,
                sequentClass, String.class).invoke(null, env, sequent, proofName);
            Object sideProof = invokeNullary(starter, "getProof");
            clazz("de.uka.ilkd.key.rule.OneStepSimplifier").getMethod("refreshOSS", proofClass)
                    .invoke(null, sideProof);
            sink.writeln("Created side proof for semantics blasting.");

            // (2) semantics blasting macro on the side proof
            // (AbstractCounterExampleGenerator.searchCounterExample,
            // AbstractCounterExampleGenerator.java:75-87)
            Object macro = clazz("de.uka.ilkd.key.testgen.macros.SemanticsBlastingMacro")
                    .getConstructor().newInstance();
            Object proofControl = invokeNullary(ui, "getProofControl");
            Object taskListener = invokeNullary(proofControl, "getDefaultProverTaskListener");
            Object openGoals = invokeNullary(sideProof, "openEnabledGoals");
            macro.getClass().getMethod("applyTo",
                clazz("de.uka.ilkd.key.control.UserInterfaceControl"), proofClass,
                clazz("org.key_project.util.collection.ImmutableList"),
                clazz("de.uka.ilkd.key.logic.PosInOccurrence"),
                clazz("org.key_project.prover.engine.ProverTaskListener")).invoke(macro, ui,
                    sideProof, openGoals, null, taskListener);
            sink.writeln("Semantics blasting finished.");

            // (3) SMT settings for the Z3 CE launch (same triple as
            // AbstractCounterExampleGenerator.java:90-92)
            Object proofSettings = invokeNullary(sideProof, "getSettings");
            Object pdSettings = invokeNullary(proofSettings, "getSMTSettings");
            Object piSettings = invokeNullary(
                Class.forName("de.uka.ilkd.key.settings.ProofIndependentSettings")
                        .getField("DEFAULT_INSTANCE").get(null),
                "getSMTSettings");
            Object newSettings = invokeNullary(proofSettings, "getNewSMTSettings");
            Object smtSettings = clazz("de.uka.ilkd.key.settings.DefaultSMTSettings")
                    .getConstructor(clazz("de.uka.ilkd.key.settings.ProofDependentSMTSettings"),
                        clazz("de.uka.ilkd.key.settings.ProofIndependentSMTSettings"),
                        clazz("de.uka.ilkd.key.settings.NewSMTTranslationSettings"), proofClass)
                    .newInstance(pdSettings, piSettings, newSettings, sideProof);

            // (4) launch Z3 CE with a reflective SolverLauncherListener
            // (AbstractCounterExampleGenerator.java:93-99)
            Object launcher = clazz("de.uka.ilkd.key.smt.SolverLauncher")
                    .getConstructor(clazz("de.uka.ilkd.key.smt.SMTSettings"))
                    .newInstance(smtSettings);
            launcherRef.set(launcher);
            Object listener = solverLauncherListenerProxy(sink);
            launcher.getClass().getMethod("addListener",
                clazz("de.uka.ilkd.key.smt.SolverLauncherListener")).invoke(launcher, listener);
            Object z3 = Class.forName("de.uka.ilkd.key.smt.solvertypes.SolverTypes")
                    .getField("Z3_CE_SOLVER").get(null);
            Collection<?> problems = (Collection<?>) clazz("de.uka.ilkd.key.smt.SMTProblem")
                    .getMethod("createSMTProblems", proofClass).invoke(null, sideProof);
            Object services = invokeNullary(sideProof, "getServices");
            launcher.getClass().getMethod("launch", Collection.class, Collection.class,
                clazz("de.uka.ilkd.key.java.Services")).invoke(launcher, List.of(z3), problems,
                    services);
            sink.finished();
        } catch (InvocationTargetException e) {
            Throwable cause = e.getCause();
            if (cause instanceof InterruptedException ie) {
                Thread.currentThread().interrupt();
                throw ie;
            }
            sink.error(cause == null ? e : cause);
        } catch (ReflectiveOperationException | RuntimeException e) {
            sink.error(e);
        }
    }

    /** Asks the running {@code SolverLauncher} to stop (the Stop button of the CE dialog). */
    static void stopLauncher(Object launcher) {
        try {
            launcher.getClass().getMethod("stop").invoke(launcher);
        } catch (ReflectiveOperationException | RuntimeException e) {
            LOGGER.warn("Could not stop the SMT launcher", e);
        }
    }

    // ------------------------------------------------------------------ listener proxies

    /**
     * A {@code java.lang.reflect.Proxy} for {@code TestGenerationLifecycleListener} (the
     * key.core.testgen interface) that forwards the events into the {@link LogSinkF}. The
     * interface is deliberately not implemented at compile time — its methods are typed with
     * key.core classes (TGPhase, Proof) that are absent from the compile classpath.
     */
    private static Object lifecycleListenerProxy(Class<?> listenerClass, LogSinkF sink) {
        return Proxy.newProxyInstance(listenerClass.getClassLoader(),
            new Class<?>[] { listenerClass },
            (proxy, method, args) -> {
                switch (method.getName()) {
                    case "writeln" -> {
                        Object message = args == null || args.length < 2 ? null : args[1];
                        sink.writeln(message == null ? "" : message.toString());
                    }
                    case "phase" -> {
                        // phase changes are not rendered, matching the Swing TGInfoDialog logger
                    }
                    case "writeException" -> sink.error(throwableOf(args));
                    case "finish" -> sink.finished();
                    case "equals" -> {
                        return args != null && args.length == 1 && args[0] == proxy;
                    }
                    case "hashCode" -> {
                        return System.identityHashCode(proxy);
                    }
                    case "toString" -> {
                        return "TestGenerationLifecycleListener(proxy)";
                    }
                    default -> {
                    }
                }
                return null;
            });
    }

    /**
     * A {@code java.lang.reflect.Proxy} for {@code SolverLauncherListener} that streams the
     * solver statistics of the counterexample search into the {@link LogSinkF}. The result
     * summary mirrors {@code AbstractTestGenerator.filterSolverResultsAndShowSolverStatistics}
     * (AbstractTestGenerator.java:383-428).
     */
    private static Object solverLauncherListenerProxy(LogSinkF sink)
            throws ClassNotFoundException {
        Class<?> listenerClass = clazz("de.uka.ilkd.key.smt.SolverLauncherListener");
        return Proxy.newProxyInstance(listenerClass.getClassLoader(),
            new Class<?>[] { listenerClass }, (proxy, method, args) -> {
                switch (method.getName()) {
                    case "launcherStarted" -> {
                        Object problems = args == null || args.length == 0 ? null : args[0];
                        int count = problems instanceof Collection<?> c ? c.size() : 0;
                        sink.writeln("Searching for counterexamples: " + count
                            + " SMT problem(s)...");
                    }
                    case "launcherStopped" -> {
                        Object solvers = args == null || args.length < 2 ? null : args[1];
                        reportSolverResults(solvers, sink);
                    }
                    case "equals" -> {
                        return args != null && args.length == 1 && args[0] == proxy;
                    }
                    case "hashCode" -> {
                        return System.identityHashCode(proxy);
                    }
                    case "toString" -> {
                        return "SolverLauncherListener(proxy)";
                    }
                    default -> {
                    }
                }
                return null;
            });
    }

    private static void reportSolverResults(@Nullable Object finishedSolvers, LogSinkF sink) {
        Collection<?> solvers = finishedSolvers instanceof Collection<?> c ? c : List.of();
        int valid = 0;
        int falsifiable = 0;
        int unknown = 0;
        for (Object solver : solvers) {
            try {
                Object result = invokeNullary(solver, "getFinalResult");
                if (result != null) {
                    Object truth = invokeNullary(result, "isValid");
                    if (truth != null) {
                        switch (truth.toString()) {
                            case "VALID" -> valid++;
                            case "FALSIFIABLE" -> falsifiable++;
                            case "UNKNOWN" -> unknown++;
                            default -> {
                            }
                        }
                    }
                }
            } catch (ReflectiveOperationException | RuntimeException ex) {
                sink.writeln("Solver exception: " + (ex.getMessage() == null
                        ? ex.getClass().getSimpleName()
                        : ex.getMessage()));
            }
        }
        sink.writeln("--- SMT Solver Results ---\n" + " solved pathconditions:" + falsifiable
            + "\n" + " invalid pre-/pathconditions:" + valid + "\n" + " unknown:" + unknown);
        sink.writeln(falsifiable > 0 ? "Found " + falsifiable + " counterexample(s)."
                : "No counterexample found for the selected goal.");
    }

    private static Throwable throwableOf(Object @Nullable [] args) {
        Object value = args == null || args.length < 2 ? null : args[1];
        return value instanceof Throwable t ? t
                : new RuntimeException("writeException without throwable: " + value);
    }

    // ------------------------------------------------------------------ low-level reflection

    private static Class<?> clazz(String name) throws ClassNotFoundException {
        return Class.forName(name);
    }

    private static @Nullable Object callNullary(@Nullable Object target, String method) {
        if (target == null) {
            return null;
        }
        try {
            return invokeNullary(target, method);
        } catch (ReflectiveOperationException | RuntimeException e) {
            LOGGER.warn("Could not invoke {}.{}()", target.getClass().getSimpleName(), method, e);
            return null;
        }
    }

    private static Object invokeNullary(Object target, String method)
            throws ReflectiveOperationException {
        return target.getClass().getMethod(method).invoke(target);
    }
}
