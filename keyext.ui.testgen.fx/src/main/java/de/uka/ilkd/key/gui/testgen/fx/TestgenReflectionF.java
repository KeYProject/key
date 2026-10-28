/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.testgen.fx;

import java.io.IOException;
import java.lang.reflect.Array;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Proxy;
import java.util.Collection;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.BooleanSupplier;
import javafx.stage.Stage;

import de.uka.ilkd.key.smt.SolverLauncherListener;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The reflective bridge to the {@code key.core.testgen} generation logic.
 * <p>
 * <b>NOT part of the SPI:</b> {@code key.core.testgen} is not on the compile classpath of this
 * module (the frozen {@code build.gradle} only exposes {@code key.ui.fx}, the Swing
 * {@code keyext.ui.testgen} and {@code key.core}; the testgen module arrives on the runtime
 * classpath of the app), so all calls into the SMT/test-case generation machinery are dispatched
 * through plain reflection — {@code key.core} types ({@code Proof}, {@code Sequent}, ...) are
 * nameable and appear as typed parameters where the callers have them at hand. The routed entry
 * points mirror the ones the Swing extension uses:
 * <ul>
 * <li>{@link #generateTestcases} — the pipeline of {@code TestgenFacade.generateTestcases}
 * (TestgenFacade.java:37-101): bounded symbolic execution (FinishSymbolicExecution / TestGen
 * macro), semantic blasting and the Z3 CE run with JUnit test-suite generation. Unlike the
 * facade the {@code SolverLauncher} is created here and handed to the caller, so the Stop button
 * can stop it like the Swing {@code TGWorker.stopSMTLauncher} (the Swing {@code TGWorker} drives
 * the same steps through {@code AbstractTestGenerator}, which needs a UI subclass that cannot be
 * materialised without the compile-time types; the facade is its headless counterpart, and its
 * hidden launcher would leave the run unstoppable).</li>
 * <li>{@link #searchCounterExample} — the counterexample search of
 * {@code AbstractSideProofCounterExampleGenerator.searchCounterExample} (side proof creation via
 * {@code SideProofUtil}, {@code SemanticsBlastingMacro} on the side proof, then Z3 CE via a
 * {@code SolverLauncher}). The abstract generator's {@code createSolverListener} hook is
 * UI-specific; the caller supplies the {@code SolverLauncherListener} (see
 * {@link #searchCounterExample} for the C4 {@code SolverListenerF} route) and this class keeps
 * the reflective log-only fallback.</li>
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
     * Runs the test-case generation, the reflective counterpart of
     * {@code TestgenFacade.generateTestcases} (TestgenFacade.java:37-101): bounded symbolic
     * execution (if enabled), the {@code TestGenMacro}, semantic blasting and the final Z3 CE
     * launch that writes the JUnit test suite into the configured output folder. Unlike the
     * facade the {@code SolverLauncher} is created here and its handle handed to the caller
     * ({@code launcherRef}), so the Stop button can stop it like the Swing
     * {@code TGWorker.stopSMTLauncher} (TGWorker.java:70 — the facade hides its launcher). The
     * phases are guarded by {@code shouldStop} (the Swing {@code StopRequest} parity,
     * TGWorker.java:31-86); the auto-mode shell lives in {@link TestGenerationTaskF} (the Swing
     * {@code TGWorker.start/done} placement).
     *
     * @param ui the UserInterfaceControl of the main window (reflected)
     * @param proof the selected proof (reflected)
     * @param shouldStop the cooperative stop flag (checked between the phases and before the
     *        launch)
     * @param sink the log sink of the run dialog
     * @param launcherRef receives the running {@code SolverLauncher}
     * @throws InterruptedException when the run was interrupted (task cancelled)
     */
    static void generateTestcases(Object ui, Object proof, BooleanSupplier shouldStop,
            LogSinkF sink, AtomicReference<@Nullable Object> launcherRef)
            throws InterruptedException {
        if (ui == null || proof == null) {
            sink.writeln("Test generation cancelled: no proof loaded.");
            return;
        }
        if (!z3CeInstalled()) {
            sink.writeln("Could not find the z3 SMT solver. Aborting.");
            return;
        }
        try {
            Class<?> proofClass = clazz("de.uka.ilkd.key.proof.Proof");
            Class<?> settingsClass = clazz("de.uka.ilkd.key.testgen.TestGenerationSettings");
            Class<?> lifecycleClass =
                clazz("de.uka.ilkd.key.testgen.smt.testgen.TestGenerationLifecycleListener");
            Class<?> tgPhaseClass = clazz("de.uka.ilkd.key.testgen.smt.testgen.TGPhase");
            Class<?> tgReporterClass = clazz("de.uka.ilkd.key.testgen.TGReporter");
            Class<?> tgClass = clazz("de.uka.ilkd.key.testgen.TestCaseGenerator");

            // reporter + generator (TestgenFacade.java:33-34)
            Object settings = settingsClass.getMethod("getInstance").invoke(null);
            Object reporter = tgReporterClass.getConstructor(lifecycleClass)
                    .newInstance(lifecycleListenerProxy(lifecycleClass, sink));
            Object tg = tgClass.getConstructor(proofClass, settingsClass, tgReporterClass)
                    .newInstance(proof, settings, reporter);

            // SMT settings triple (TestgenFacade.java:36-47); the 10 s solver timeout is the
            // facade default (TestgenFacade.java:46)
            Class<?> newSettingsClass = clazz("de.uka.ilkd.key.settings.NewSMTTranslationSettings");
            Class<?> pdClass = clazz("de.uka.ilkd.key.settings.ProofDependentSMTSettings");
            Class<?> piClass = clazz("de.uka.ilkd.key.settings.ProofIndependentSMTSettings");
            Object newSettings = newSettingsClass.getConstructor().newInstance();
            Object pdSettings = pdClass.getMethod("getDefaultSettingsData").invoke(null);
            Object piSettings = piClass.getMethod("getDefaultSettingsData").invoke(null);
            piSettings.getClass().getMethod("setTimeout", int.class).invoke(piSettings, 10000);
            Object smtSettings = clazz("de.uka.ilkd.key.settings.DefaultSMTSettings")
                    .getConstructor(pdClass, piClass, newSettingsClass, proofClass)
                    .newInstance(pdSettings, piSettings, newSettings, proof);

            // own SolverLauncher (TestgenFacade.java:49) — the handle goes into launcherRef so
            // the Stop button can stop it; the JUnit test-suite generation runs in the
            // launcherStopped event (TestgenFacade.java:50-65)
            Object launcher = clazz("de.uka.ilkd.key.smt.SolverLauncher")
                    .getConstructor(clazz("de.uka.ilkd.key.smt.SMTSettings"))
                    .newInstance(smtSettings);
            launcherRef.set(launcher);
            Class<?> launcherListenerClass = clazz("de.uka.ilkd.key.smt.SolverLauncherListener");
            launcher.getClass().getMethod("addListener", launcherListenerClass).invoke(launcher,
                testSuiteListenerProxy(launcherListenerClass, tg, tgReporterClass, reporter));

            Object taskListener = invokeNullary(invokeNullary(ui, "getProofControl"),
                "getDefaultProverTaskListener");
            Object goals = invokeNullary(proof, "openEnabledGoals");

            // phase 1: bounded symbolic execution (TestgenFacade.java:69-74)
            if ((Boolean) settingsClass.getMethod("getApplySymbolicExecution").invoke(settings)) {
                if (stopped(shouldStop)) {
                    return;
                }
                invokeApplyTo(clazz("de.uka.ilkd.key.macros.FinishSymbolicExecutionMacro")
                        .getConstructor().newInstance(),
                    ui, proof, goals, taskListener);
            }

            // phase 2: the TestGen macro (TestgenFacade.java:76-78)
            if (stopped(shouldStop)) {
                return;
            }
            Object tgMacro = clazz("de.uka.ilkd.key.testgen.macros.TestGenMacro")
                    .getConstructor(int.class)
                    .newInstance(settingsClass.getMethod("getMaximalUnwinds").invoke(settings));
            invokeApplyTo(tgMacro, ui, proof, goals, taskListener);

            // phase 3: semantic blasting (TestgenFacade.java:80-82)
            if (stopped(shouldStop)) {
                return;
            }
            invokeApplyTo(clazz("de.uka.ilkd.key.testgen.macros.SemanticsBlastingMacro")
                    .getConstructor().newInstance(),
                ui, proof, goals, taskListener);

            // phase 4: the synchronous Z3 CE launch (TestgenFacade.java:84-86)
            if (stopped(shouldStop)) {
                return;
            }
            Object z3 = Class.forName("de.uka.ilkd.key.smt.solvertypes.SolverTypes")
                    .getField("Z3_CE_SOLVER").get(null);
            Collection<?> problems = (Collection<?>) clazz("de.uka.ilkd.key.smt.SMTProblem")
                    .getMethod("createSMTProblems", proofClass).invoke(null, proof);
            launcher.getClass().getMethod("launch", Collection.class, Collection.class,
                clazz("de.uka.ilkd.key.java.Services")).invoke(launcher, List.of(z3), problems,
                    invokeNullary(proof, "getServices"));

            // finish events (TestgenFacade.java:88-89); the TGPhase.FINISHED goes through the
            // TGReporter and fires sink.finished() via the lifecycle proxy
            Object phase = tgPhaseClass.getField("FINISHED").get(null);
            tgReporterClass.getMethod("phase", tgPhaseClass).invoke(reporter, phase);
            tgReporterClass.getMethod("finish").invoke(reporter);
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

    /**
     * The cooperative stop check between the phases (the Swing {@code StopRequest.shouldStop}
     * plus the thread-interrupt backup, TGWorker.java:66-71 + AbstractTestGenerator.java:109).
     *
     * @return {@code true} when the run should stop
     */
    private static boolean stopped(BooleanSupplier shouldStop) {
        return shouldStop.getAsBoolean() || Thread.currentThread().isInterrupted();
    }

    /**
     * Invokes {@code macro.applyTo(ui, proof, goals, null, taskListener)} — the shared
     * {@code ProofMacro.applyTo} signature of the three generation phases.
     */
    private static void invokeApplyTo(Object macro, Object ui, Object proof, Object goals,
            Object taskListener) throws ReflectiveOperationException {
        macro.getClass().getMethod("applyTo",
            clazz("de.uka.ilkd.key.control.UserInterfaceControl"),
            clazz("de.uka.ilkd.key.proof.Proof"),
            clazz("org.key_project.util.collection.ImmutableList"),
            clazz("de.uka.ilkd.key.logic.PosInOccurrence"),
            clazz("org.key_project.prover.engine.ProverTaskListener")).invoke(macro, ui, proof,
                goals, null, taskListener);
    }

    // ------------------------------------------------------------------ counterexample search

    /**
     * The {@code SolverLauncherListener} factory of the counterexample search — the
     * UI-specific {@code createSolverListener} hook of
     * {@code AbstractSideProofCounterExampleGenerator} (AbstractSideProofCounterExampleGenerator
     * .java:22-27): the {@code SolverLauncherListener} for the given {@code DefaultSMTSettings}
     * (first argument) and side {@code Proof} (second argument).
     */
    @FunctionalInterface
    interface SolverListenerFactoryF {
        SolverLauncherListener create(Object settings, Object sideProof);
    }

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
     * The {@code SolverLauncherListener} comes from {@code listenerFactory} (the
     * {@code createSolverListener} parity hook): {@link CounterExampleTaskF} supplies a
     * {@code SolverListenerF}, which opens the modal progress dialog and the results
     * (counterexample model) like the Swing {@code SolverListener}.
     *
     * @param ui the UserInterfaceControl of the main window (reflected)
     * @param proof the proof of the selected goal (reflected)
     * @param sequent the sequent of the selected goal (reflected)
     * @param sink the log sink of the run dialog (the pipeline messages)
     * @param launcherRef receives the running {@code SolverLauncher} so the Stop button can ask it
     *        to stop
     * @param listenerFactory creates the {@code SolverLauncherListener} for the given
     *        {@code DefaultSMTSettings} and side proof
     * @throws InterruptedException when the run was interrupted (task cancelled)
     */
    static void searchCounterExample(Object ui, Object proof, Object sequent, LogSinkF sink,
            AtomicReference<@Nullable Object> launcherRef, SolverListenerFactoryF listenerFactory)
            throws InterruptedException {
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

            // (4) launch Z3 CE with the caller's SolverLauncherListener
            // (AbstractCounterExampleGenerator.java:93-99)
            Object launcher = clazz("de.uka.ilkd.key.smt.SolverLauncher")
                    .getConstructor(clazz("de.uka.ilkd.key.smt.SMTSettings"))
                    .newInstance(smtSettings);
            launcherRef.set(launcher);
            launcher.getClass().getMethod("addListener",
                clazz("de.uka.ilkd.key.smt.SolverLauncherListener"))
                    .invoke(launcher, listenerFactory.create(smtSettings, sideProof));
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
     * A {@code java.lang.reflect.Proxy} for {@code SolverLauncherListener} that runs the JUnit
     * test-suite generation on the finished solvers (the anonymous listener of
     * {@code TestgenFacade.generateTestcases}, TestgenFacade.java:50-65: the first solver's
     * exception is re-thrown, then {@code TestCaseGenerator.generateJUnitTestSuite} and the
     * "Compile the generated files" hint; NoSuchElement/IO go to the reporter like in Swing).
     */
    private static Object testSuiteListenerProxy(Class<?> listenerClass, Object testGenerator,
            Class<?> tgReporterClass, Object reporter) {
        return Proxy.newProxyInstance(listenerClass.getClassLoader(),
            new Class<?>[] { listenerClass }, (proxy, method, args) -> {
                switch (method.getName()) {
                    case "launcherStopped" -> {
                        Object solvers = args == null || args.length < 2 ? null : args[1];
                        Collection<?> finished = solvers instanceof Collection<?> c ? c
                                : List.of();
                        try {
                            Object first = finished.iterator().next();
                            Object exception = callNullary(first, "getException");
                            if (exception != null) {
                                throw new RuntimeException("Exception during SMT",
                                    (Throwable) exception);
                            }
                            testGenerator.getClass()
                                    .getMethod("generateJUnitTestSuite", Collection.class)
                                    .invoke(testGenerator, finished);
                            tgReporterClass.getMethod("writeln", String.class).invoke(reporter,
                                "Compile the generated files using a Java compiler.");
                        } catch (NoSuchElementException e) {
                            reportException(tgReporterClass, reporter, e);
                        } catch (InvocationTargetException e) {
                            Throwable cause = e.getCause();
                            if (cause instanceof NoSuchElementException
                                    || cause instanceof IOException) {
                                reportException(tgReporterClass, reporter, cause);
                            } else {
                                throw cause == null ? e : cause;
                            }
                        } catch (ReflectiveOperationException e) {
                            LOGGER.warn("Could not generate the JUnit test suite", e);
                        }
                    }
                    case "equals" -> {
                        return args != null && args.length == 1 && args[0] == proxy;
                    }
                    case "hashCode" -> {
                        return System.identityHashCode(proxy);
                    }
                    case "toString" -> {
                        return "SolverLauncherListener(testSuite proxy)";
                    }
                    default -> {
                    }
                }
                return null;
            });
    }

    /** {@code TGReporter.reportException} (TestgenFacade.java:63-64). */
    private static void reportException(Class<?> tgReporterClass, Object reporter,
            Throwable throwable) {
        try {
            tgReporterClass.getMethod("reportException", Exception.class).invoke(reporter,
                throwable);
        } catch (ReflectiveOperationException | RuntimeException e) {
            LOGGER.warn("Could not report the test-generation exception", e);
        }
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
