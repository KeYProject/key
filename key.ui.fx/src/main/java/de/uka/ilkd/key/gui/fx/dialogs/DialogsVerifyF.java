/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.dialogs;

import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;
import javafx.application.Platform;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.InteractiveRuleApplicationCompletionF;
import de.uka.ilkd.key.gui.fx.WindowUserInterfaceControlF;
import de.uka.ilkd.key.gui.fx.contractcompletions.BlockContractExternalCompletionF;
import de.uka.ilkd.key.gui.fx.contractcompletions.BlockContractInternalCompletionF;
import de.uka.ilkd.key.gui.fx.contractcompletions.ContractConfiguratorF;
import de.uka.ilkd.key.gui.fx.contractcompletions.DependencyContractCompletionF;
import de.uka.ilkd.key.gui.fx.contractcompletions.FunctionalOperationContractCompletionF;
import de.uka.ilkd.key.gui.fx.contractcompletions.InvariantConfiguratorF;
import de.uka.ilkd.key.gui.fx.contractcompletions.LoopInvariantRuleCompletionF;
import de.uka.ilkd.key.gui.fx.mergerule.MergeRuleCompletionF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF.Kind;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.TacletInfo;

import org.key_project.util.collection.ImmutableSet;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * dialogs (P2b): interactive self test for the contract-completion dialogs and the lemma
 * dialogs ({@code key.fx.verify.dialogs}, forwarded by {@code key.ui.fx/build.gradle}),
 * dispatched from the main window after the demo load. The harness
 * <ol>
 * <li>checks the interactive-completion registry: the six Swing-registered completions of
 * {@code WindowUserInterfaceControl} (merge + the five contract/invariant completions, P2b) are
 * registered with the FX control in {@code MainWindowF} (Swing WindowUserInterfaceControl
 * .java:74-82);</li>
 * <li>exercises the {@link ItemChooserF} dual-list semantics ({@code setItems} select-all +
 * name sort, user filters, side moves, {@code getDataOfSelectedItems});</li>
 * <li>opens the {@link ContractConfiguratorF} and the auxiliary (block-contract)
 * {@code AuxiliaryContractConfiguratorF} non-blocking and drives Cancel and OK through the
 * {@code requestCancel}/{@code requestOk} seams (the OK path sets {@code wasSuccessful});</li>
 * <li>runs the {@link LemmaSelectionDialogF} {@code TacletFilter} end to end from a background
 * thread (the thread the {@code TacletSoundnessPOLoader} calls it on): cancel leaves the whole
 * choice on the left (empty selection), OK after moving all returned taclets to the right
 * returns exactly them;</li>
 * <li>checks the {@link InvariantConfiguratorF} singleton and the abbreviation-map wiring is in
 * place (the modal invariant editor itself needs an interactive loop application — not
 * headless-drivable, see the P2b note in PARITY-SIGNOFF.md).</li>
 * </ol>
 */
public final class DialogsVerifyF {

    private static final Logger LOGGER = LoggerFactory.getLogger(DialogsVerifyF.class);

    private DialogsVerifyF() {
    }

    /**
     * Runs the self test. Must be called on the FX thread (from the {@code key.fx.verify.dialogs}
     * dispatch in the main window).
     *
     * @param owner the owner window (unused; kept for API symmetry with the other harnesses)
     * @param proof the loaded demo proof (its services and init-config taclets feed the
     *        skeletons), may be {@code null}
     * @param ui the FX user interface control with the completion registry
     * @return the report (PASS / FAIL with a reason); a missing proof yields SKIP
     */
    public static String run(Window owner, Proof proof, WindowUserInterfaceControlF ui) {
        if (proof == null) {
            LOGGER.warn("Dialogs verification: no proof loaded — SKIP");
            return "SKIP (no proof)";
        }
        Thread worker = new Thread(() -> {
            String report = runAll(proof, ui);
            LOGGER.info("Dialogs verification: {}", report);
            Platform.runLater(() -> NotificationManagerF.getInstance()
                    .notify("Dialogs verification: " + report,
                        report.startsWith("PASS") ? Kind.INFO : Kind.ERROR));
        }, "fx-verify-dialogs");
        worker.setDaemon(true);
        worker.start();
        return "running (see log)";
    }

    private static String runAll(Proof proof, WindowUserInterfaceControlF ui) {
        StringBuilder problems = new StringBuilder();

        verifyRegistry(ui, problems);
        verifyItemChooser(problems);
        verifyContractConfigurator(proof, problems);
        verifyAuxiliaryContractConfigurator(proof, problems);
        verifyLemmaSelectionDialog(proof, problems);
        verifyInvariantConfiguratorWiring(problems);

        if (problems.length() > 0) {
            return "FAIL: " + problems;
        }
        return "PASS: registry (6 completions), item chooser, contract configurator, auxiliary"
            + " configurator, lemma selection dialog, invariant configurator wiring";
    }

    /** Step 1: the interactive-completion registry of the FX user interface control. */
    private static void verifyRegistry(WindowUserInterfaceControlF ui, StringBuilder problems) {
        List<InteractiveRuleApplicationCompletionF> completions = ui.getCompletions();
        // the five P2b completions plus the P1 merge completion (Swing WindowUserInterfaceControl
        // .java:74-82 registers 10 in total; the four merge variants and the access/field
        // completions are registered in later batches — the FX port lists what exists to date)
        final Class<?>[] expected = {
            MergeRuleCompletionF.class, FunctionalOperationContractCompletionF.class,
            DependencyContractCompletionF.class, LoopInvariantRuleCompletionF.class,
            BlockContractInternalCompletionF.class, BlockContractExternalCompletionF.class
        };
        for (Class<?> clazz : expected) {
            boolean found = false;
            for (InteractiveRuleApplicationCompletionF c : completions) {
                if (clazz.isInstance(c)) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                problems.append("completion not registered: ").append(clazz.getSimpleName())
                        .append("; ");
            }
        }
        if (completions.isEmpty()) {
            problems.append("completion registry empty; ");
        }
    }

    /** Step 2: the {@link ItemChooserF} dual-list semantics (pure UI, no services). */
    private static void verifyItemChooser(StringBuilder problems) {
        runOnFx(() -> {
            ItemChooserF<String> chooser = new ItemChooserF<>("Search");
            List<String> data = List.of("beta taclet", "alpha taclet", "gamma taclet");
            chooser.setItems(data, "Taclets");
            // Swing: all items start on the LEFT and the supplied list is select-all'ed; the FX
            // lists sort by the lower-case name (Swing TableRowSorter)
            if (!chooser.getDataOfSelectedItems().isEmpty()) {
                problems.append("item chooser: initial selection not empty; ");
            }
            chooser.moveAllToRight();
            List<String> selected = chooser.getDataOfSelectedItems();
            if (!selected.contains("alpha taclet") || !selected.contains("beta taclet")
                    || !selected.contains("gamma taclet") || selected.size() != 3) {
                problems.append("item chooser: moveAllToRight lost items; ");
            }
            // Swing RowFilter: user filters hide items on both sides
            chooser.addFilter(item -> item.contains("beta"));
            chooser.moveAllToLeft();
            if (!chooser.getDataOfSelectedItems().isEmpty()) {
                problems.append("item chooser: filter did not apply to the right side; ");
            }
            chooser.removeFilter(item -> item.contains("beta"));
            chooser.moveAllToRight();
            if (chooser.getDataOfSelectedItems().size() != 3) {
                problems.append("item chooser: removed filter not re-applied; ");
            }
            chooser.moveAllToLeft();
            if (chooser.getDataOfSelectedItems().size() != 0) {
                problems.append("item chooser: moveAllToLeft left items behind; ");
            }
        });
    }

    /** Step 3a: the {@link ContractConfiguratorF} open / cancel / OK skeleton. */
    private static void verifyContractConfigurator(Proof proof, StringBuilder problems) {
        ContractConfiguratorF[] ref = new ContractConfiguratorF[1];
        // cancel round
        runOnFx(() -> ref[0] = new ContractConfiguratorF(proof.getServices(),
            new de.uka.ilkd.key.speclang.Contract[0], "Contracts for <none>", true));
        runOnFx(ref[0]::showNonBlocking);
        waitUntil(() -> ref[0].getStage().isShowing(), "contract configurator shows", problems);
        runOnFx(ref[0]::requestCancel);
        waitUntil(() -> !ref[0].getStage().isShowing(), "contract configurator closes on cancel",
            problems);
        if (ref[0].wasSuccessful()) {
            problems.append("contract configurator: cancel marked successful; ");
        }
        // ok round
        runOnFx(() -> ref[0] = new ContractConfiguratorF(proof.getServices(),
            new de.uka.ilkd.key.speclang.Contract[0], "Contracts for <none>", true));
        runOnFx(ref[0]::showNonBlocking);
        waitUntil(() -> ref[0].getStage().isShowing(), "contract configurator shows (2)",
            problems);
        runOnFx(ref[0]::requestOk);
        waitUntil(() -> !ref[0].getStage().isShowing(), "contract configurator closes on ok",
            problems);
        if (!ref[0].wasSuccessful()) {
            problems.append("contract configurator: ok not marked successful; ");
        }
    }

    /** Step 3b: the auxiliary (block-contract) configurator skeleton. */
    private static void verifyAuxiliaryContractConfigurator(Proof proof,
            StringBuilder problems) {
        de.uka.ilkd.key.gui.fx.contractcompletions.AuxiliaryContractConfiguratorF<de.uka.ilkd.key.speclang.BlockContract>[] ref =
            new de.uka.ilkd.key.gui.fx.contractcompletions.AuxiliaryContractConfiguratorF[1];
        runOnFx(() -> ref[0] =
            new de.uka.ilkd.key.gui.fx.contractcompletions.AuxiliaryContractConfiguratorF<>(
                "Block Contract Configurator",
                new de.uka.ilkd.key.gui.fx.contractcompletions.BlockContractSelectionPanelF(
                    proof.getServices(), true),
                proof.getServices(), new de.uka.ilkd.key.speclang.BlockContract[0],
                "Contracts for Block: <none>"));
        runOnFx(ref[0]::showNonBlocking);
        if (!waitUntil(() -> ref[0].getStage().isShowing(), "auxiliary configurator shows",
            problems)) {
            return;
        }
        runOnFx(ref[0]::requestCancel);
        waitUntil(() -> !ref[0].getStage().isShowing(),
            "auxiliary configurator closes on cancel", problems);
        if (ref[0].wasSuccessful()) {
            problems.append("auxiliary configurator: cancel marked successful; ");
        }
    }

    /**
     * Step 4: the {@link LemmaSelectionDialogF} {@code TacletFilter} — called from a background
     * thread like the {@code TacletSoundnessPOLoader} does; the harness drives the OK/Cancel
     * seams from the FX thread while the modal dialog blocks it.
     */
    private static void verifyLemmaSelectionDialog(Proof proof, StringBuilder problems) {
        var taclets = proof.getInitConfig().getTaclets();
        if (taclets.isEmpty()) {
            problems.append("lemma dialog: no taclets in the init config; ");
            return;
        }
        Taclet taclet = taclets.get(0);
        List<TacletInfo> infos =
            List.of(new TacletInfo(taclet, false, false), new TacletInfo(taclet, false, true));

        // round 1: cancel → nothing is selected
        LemmaSelectionDialogF[] dialogRef = new LemmaSelectionDialogF[1];
        runOnFx(() -> dialogRef[0] = new LemmaSelectionDialogF());
        LemmaSelectionDialogF dialog = dialogRef[0];
        AtomicInteger failures = new AtomicInteger();
        CountDownLatch done = new CountDownLatch(1);
        runFilterThread(dialog, infos, done, failures);
        waitUntil(dialog::isShowing, "lemma selection dialog shows", problems);
        Platform.runLater(dialog::requestCancel);
        awaitLatch(done, "lemma selection dialog cancels", failures);
        if (failures.get() > 0) {
            problems.append("lemma dialog cancel round: ").append(failures.get())
                    .append(" failure(s); ");
        }
        if (!dialog.isCancelled()) {
            problems.append("lemma dialog cancel round: cancelled flag not set; ");
        }

        // round 2: move all supported taclets to the right, then OK → exactly those are selected
        LemmaSelectionDialogF[] dialog2Ref = new LemmaSelectionDialogF[1];
        runOnFx(() -> dialog2Ref[0] = new LemmaSelectionDialogF());
        LemmaSelectionDialogF dialog2 = dialog2Ref[0];
        CountDownLatch done2 = new CountDownLatch(1);
        AtomicInteger failures2 = new AtomicInteger();
        runFilterThread(dialog2, infos, done2, failures2);
        waitUntil(dialog2::isShowing, "lemma selection dialog shows (2)", problems);
        // the unsupported info is filtered for moving (Swing filterForMovingTaclets): only the
        // supported one may reach the right side
        Platform.runLater(() -> {
            ItemChooserF<TacletInfo> chooser = dialog2.getTacletChooser();
            chooser.moveAllToRight();
            Platform.runLater(dialog2::requestOk);
        });
        awaitLatch(done2, "lemma selection dialog ok", failures2);
        if (failures2.get() > 0) {
            problems.append("lemma dialog ok round: ").append(failures2.get())
                    .append(" failure(s); ");
        }
        ImmutableSet<Taclet> selectedSet = dialog2.lastFilterResult();
        if (selectedSet == null || !selectedSet.contains(taclet) || selectedSet.size() != 1) {
            problems.append("lemma dialog ok round: unexpected selection (size "
                + (selectedSet == null ? "null" : selectedSet.size()) + "); ");
        }
    }

    private static void runFilterThread(LemmaSelectionDialogF dialog, List<TacletInfo> infos,
            CountDownLatch done, AtomicInteger failures) {
        Thread t = new Thread(() -> {
            try {
                dialog.filter(infos);
            } catch (Throwable e) {
                LOGGER.warn("Dialogs verification: lemma filter thread failed", e);
                failures.incrementAndGet();
            } finally {
                done.countDown();
            }
        }, "fx-verify-dialogs-lemma");
        t.setDaemon(true);
        t.start();
    }

    /** Step 5: the invariant configurator singleton + abbrev map wiring are in place. */
    private static void verifyInvariantConfiguratorWiring(StringBuilder problems) {
        InvariantConfiguratorF configurator = InvariantConfiguratorF.getInstance();
        if (configurator == null) {
            problems.append("invariant configurator: singleton null; ");
        }
        if (InvariantConfiguratorF.getAbbrevMap() == null) {
            problems.append("invariant configurator: abbrev map not wired; ");
        }
    }

    /** Polls a condition with a timeout (the FX runLater queue keeps the modal loop alive). */
    private static boolean waitUntil(java.util.function.BooleanSupplier condition, String what,
            StringBuilder problems) {
        long deadline = System.currentTimeMillis() + 10_000;
        while (System.currentTimeMillis() < deadline && !condition.getAsBoolean()) {
            try {
                Thread.sleep(25);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                problems.append("interrupted waiting for ").append(what).append("; ");
                return false;
            }
        }
        if (!condition.getAsBoolean()) {
            problems.append("timed out waiting for ").append(what).append("; ");
            return false;
        }
        return true;
    }

    /** Runs {@code runnable} on the FX thread and blocks until it completed. */
    private static void runOnFx(Runnable runnable) {
        if (Platform.isFxApplicationThread()) {
            runnable.run();
            return;
        }
        CountDownLatch latch = new CountDownLatch(1);
        Platform.runLater(() -> {
            try {
                runnable.run();
            } finally {
                latch.countDown();
            }
        });
        awaitLatch(latch, "runnable on the FX thread", null);
    }

    private static void awaitLatch(CountDownLatch latch, String what, AtomicInteger failures) {
        try {
            if (!latch.await(10, TimeUnit.SECONDS)) {
                if (failures != null) {
                    failures.incrementAndGet();
                }
                LOGGER.warn("Dialogs verification: timed out waiting for {}", what);
            }
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            if (failures != null) {
                failures.incrementAndGet();
            }
        }
    }
}
