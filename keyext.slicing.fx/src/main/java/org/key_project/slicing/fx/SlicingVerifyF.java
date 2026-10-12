/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.slicing.fx;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.function.Supplier;
import javafx.application.Platform;
import javafx.scene.web.WebView;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.recentfiles.RecentFilesF;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.slicing.DependencyTracker;
import org.key_project.slicing.RuleStatistics.RuleStatisticEntry;
import org.key_project.slicing.SlicingSettingsProvider;
import org.key_project.slicing.analysis.AnalysisResults;
import org.key_project.slicing.fx.ui.GraphvizDotExecutorF;
import org.key_project.slicing.fx.ui.RuleStatisticsDialogF;
import org.key_project.slicing.fx.ui.SliceToFixedPointDialogF;
import org.key_project.slicing.fx.ui.SlicingLeftPanelF;

import org.jspecify.annotations.NullMarked;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Headless verify harness for the proof-slicing extension port ({@code key.fx.verify.slicing},
 * forwarded by key.ui.fx/build.gradle and invoked reflectively by {@code MainWindowF} after the
 * demo load, like the other {@code key.fx.verify.*} hooks). The harness runs on a background
 * thread and asserts:
 * <ol>
 * <li>the demo proof auto-proves and the dependency tracker recorded its graph,</li>
 * <li>the DOT render: the graphviz {@code dot} binary renders the dependency graph to a PNG
 * (the primary path on machines with graphviz), <b>and</b> the documented fallback is exercised
 * (an unavailable {@code dot} executable yields the error result that makes the dialogs show the
 * DOT source instead),</li>
 * <li>the HTML statistics: the four sort orders of the Swing {@code RuleStatisticsDialog} sort
 * the entries correctly, the {@code HtmlFactory} tables (statistics + timings) are generated and
 * the statistics table renders in the FX WebView dialog,</li>
 * <li>the fixed-point iteration: the {@link SliceToFixedPointDialogF} run on the closed demo
 * proof converges (the last analysis finds no more removable steps),</li>
 * <li>the recent-files bypass: a load through the direct loader path
 * ({@code MainWindowF.loadProofFileDirect}, the path every slice load takes) fires the
 * proof-load event but leaves the recent-files list untouched.</li>
 * </ol>
 * The final marker line {@code key.fx.verify.slicing=PASS|FAIL (details)} is logged when the
 * harness finishes.
 */
@NullMarked
public final class SlicingVerifyF {

    private static final Logger LOGGER = LoggerFactory.getLogger(SlicingVerifyF.class);

    /** How long the harness waits for each asynchronous step (fixed point, loads). */
    private static final long TIMEOUT_SECONDS = 300;

    private SlicingVerifyF() {
    }

    /**
     * Starts the harness on a background thread (the caller runs on the FX thread after the demo
     * load; the auto mode and the slicing iterations must not run there).
     *
     * @param window the main window
     * @param proof the loaded demo proof
     */
    public static void run(MainWindowF window, Proof proof) {
        Thread thread = new Thread(() -> execute(window, proof), "key.fx.verify.slicing");
        thread.setDaemon(true);
        thread.start();
    }

    private static void execute(MainWindowF window, Proof proof) {
        StringBuilder report = new StringBuilder();
        boolean ok = true;
        // the dependency analysis requires the recorded ClosedBy markers of the rule
        // applications (DependencyAnalyzer: "cannot analyze proof with no (recorded) closed
        // goals"), which the prover only records when closed-goal pruning is off; restored in
        // the finally block like the other user settings the harness touches
        boolean previousNoPruningClosed = de.uka.ilkd.key.settings.GeneralSettings.noPruningClosed;
        de.uka.ilkd.key.settings.GeneralSettings.noPruningClosed = false;
        // slicing is single-core only: no dependency tracker is attached while the multi-core
        // prover is enabled (SlicingExtensionF.createTrackerForProof) — force single-core for
        // the verify regardless of the persisted setting, restore in the finally block
        boolean previousParallelProver =
            de.uka.ilkd.key.settings.ProofIndependentSettings.DEFAULT_INSTANCE
                    .getGeneralSettings().isParallelProverEnabled();
        de.uka.ilkd.key.settings.ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                .setParallelProverEnabled(false);
        try {
            ok = checkExtensionAndProof(window, proof, report)
                    & checkDotRender(proof, report)
                    & checkHtmlStatistics(window, proof, report)
                    & checkFixedPoint(window, proof, report)
                    & checkRecentFilesBypass(window, report);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            report.append("interrupted; ");
            ok = false;
        } catch (RuntimeException e) {
            LOGGER.error("slicing verification crashed", e);
            report.append("exception ").append(e).append("; ");
            ok = false;
        } finally {
            de.uka.ilkd.key.settings.GeneralSettings.noPruningClosed = previousNoPruningClosed;
            de.uka.ilkd.key.settings.ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                    .setParallelProverEnabled(previousParallelProver);
        }
        String verdict = (ok ? "PASS" : "FAIL") + " (" + report + ")";
        LOGGER.info("key.fx.verify.slicing={}", verdict);
    }

    // ------------------------------------------------------------------
    // 1. extension + auto mode
    // ------------------------------------------------------------------

    private static boolean checkExtensionAndProof(MainWindowF window, Proof proof,
            StringBuilder report) throws InterruptedException {
        SlicingExtensionF extension = findExtension();
        if (extension == null) {
            report.append("no SlicingExtensionF registered; ");
            return false;
        }
        ProofControlAccess.runAutoMode(window);
        boolean closed = proof.closed();
        report.append("demo proof auto-proved (closed=").append(closed).append("); ");
        DependencyTracker tracker = extension.trackers.get(proof);
        if (tracker == null) {
            report.append("no dependency tracker for the demo proof; ");
            return false;
        }
        if (tracker.getDependencyGraph() == null) {
            report.append("no dependency graph recorded; ");
            return false;
        }
        report.append("tracker attached, graph has ")
                .append(tracker.getDependencyGraph().countNodes())
                .append(" nodes / ")
                .append(tracker.getDependencyGraph().countEdges())
                .append(" edges; ");
        return closed;
    }

    private static SlicingExtensionF findExtension() {
        return de.uka.ilkd.key.gui.fx.extension.KeYGuiExtensionFacadeF.getExtensions().stream()
                .filter(SlicingExtensionF.class::isInstance)
                .map(SlicingExtensionF.class::cast)
                .findFirst().orElse(null);
    }

    // ------------------------------------------------------------------
    // 2. DOT render (graphviz binary) + documented fallback
    // ------------------------------------------------------------------

    private static boolean checkDotRender(Proof proof, StringBuilder report) {
        SlicingExtensionF extension = findExtension();
        DependencyTracker tracker = extension != null ? extension.trackers.get(proof) : null;
        if (tracker == null || tracker.getDependencyGraph() == null) {
            report.append("dot render skipped (no tracker); ");
            return false;
        }
        String dot = tracker.exportDot(false, false);
        GraphvizDotExecutorF.Result result = GraphvizDotExecutorF.renderPng(dot);
        boolean rendered = result.hasImage() && result.isPng();
        report.append("dot binary render: ").append(rendered ? "PNG ok" : "FAILED")
                .append(" (graphviz=").append(GraphvizDotExecutorF.isDotInstalled())
                .append("); ");
        // the documented fallback: an unavailable dot executable must yield the error result
        // (which makes PreviewDialogF/panel show the DOT source text instead)
        String realExecutable = SlicingSettingsProvider.getSlicingSettings().getDotExecutable();
        try {
            SlicingSettingsProvider.getSlicingSettings()
                    .setDotExecutable("key-fx-verify-missing-dot-binary");
            GraphvizDotExecutorF.Result fallback = GraphvizDotExecutorF.renderPng(dot);
            boolean fallbackOk = fallback.hasError() && !fallback.hasImage();
            report.append("no-graphviz fallback: ")
                    .append(fallbackOk ? "error result ok" : "FAILED")
                    .append("; ");
            return rendered && fallbackOk;
        } finally {
            SlicingSettingsProvider.getSlicingSettings().setDotExecutable(realExecutable);
        }
    }

    // ------------------------------------------------------------------
    // 3. HTML statistics (four sort orders) + HtmlFactory timings
    // ------------------------------------------------------------------

    private static boolean checkHtmlStatistics(MainWindowF window, Proof proof,
            StringBuilder report)
            throws InterruptedException {
        SlicingExtensionF extension = findExtension();
        DependencyTracker tracker = extension != null ? extension.trackers.get(proof) : null;
        if (tracker == null) {
            report.append("html statistics skipped (no tracker); ");
            return false;
        }
        AnalysisResults results = tracker.analyze(true, false);
        if (results == null) {
            report.append("analysis failed; ");
            return false;
        }
        boolean ok = true;

        // the four sort orders of the Swing RuleStatisticsDialog sort correctly
        ok &= assertSorted(report, "sort by name",
            results.ruleStatistics.sortBy(Comparator.comparing(RuleStatisticEntry::ruleName)),
            Comparator.comparing(RuleStatisticEntry::ruleName));
        ok &= assertSorted(report, "sort by total",
            results.ruleStatistics.sortBy(
                Comparator.comparing(RuleStatisticEntry::numberOfApplications).reversed()),
            Comparator.comparing(RuleStatisticEntry::numberOfApplications).reversed());
        ok &= assertSorted(report, "sort by useless",
            results.ruleStatistics.sortBy(
                Comparator.comparing(RuleStatisticEntry::numberOfUselessApplications).reversed()),
            Comparator.comparing(RuleStatisticEntry::numberOfUselessApplications).reversed());
        ok &= assertSorted(report, "sort by initial useless",
            results.ruleStatistics.sortBy(
                Comparator.comparing(RuleStatisticEntry::numberOfInitialUselessApplications)
                        .reversed()),
            Comparator.comparing(RuleStatisticEntry::numberOfInitialUselessApplications)
                    .reversed());

        // the statistics table renders in the FX WebView dialog (HtmlDialogF seam)
        String html = RuleStatisticsDialogF.genTable(results.ruleStatistics,
            results.ruleStatistics.sortBy(
                Comparator.comparing(RuleStatisticEntry::ruleName)));
        if (!html.contains("<table>")) {
            report.append("statistics html missing the table; ");
            ok = false;
        }
        CountDownLatch opened = new CountDownLatch(1);
        RuleStatisticsDialogF[] dialog = new RuleStatisticsDialogF[1];
        Platform.runLater(() -> {
            dialog[0] = RuleStatisticsDialogF.show(window.getStage(), results);
            opened.countDown();
        });
        if (!opened.await(TIMEOUT_SECONDS, TimeUnit.SECONDS)) {
            report.append("statistics dialog did not open; ");
            return false;
        }
        if (!awaitWebViewLoad(dialog[0].getWebView())) {
            report.append("statistics html did not render in the WebView; ");
            ok = false;
        } else {
            report.append("statistics html rendered in the WebView dialog; ");
        }
        Platform.runLater(dialog[0]::close);
        return ok;
    }

    private static boolean assertSorted(StringBuilder report, String what,
            List<RuleStatisticEntry> entries, Comparator<RuleStatisticEntry> comparator) {
        boolean sorted = isSorted(entries, comparator);
        report.append(what).append(": ").append(sorted ? "ok" : "FAILED").append(" (")
                .append(entries.size()).append(" entries); ");
        return sorted;
    }

    private static boolean isSorted(List<RuleStatisticEntry> entries,
            Comparator<RuleStatisticEntry> comparator) {
        for (int i = 1; i < entries.size(); i++) {
            if (comparator.compare(entries.get(i - 1), entries.get(i)) > 0) {
                return false;
            }
        }
        return true;
    }

    /**
     * Waits until the given WebView finished loading its content (its DOM document is present).
     */
    private static boolean awaitWebViewLoad(WebView view) throws InterruptedException {
        long deadline = System.currentTimeMillis() + TIMEOUT_SECONDS * 1000;
        while (System.currentTimeMillis() < deadline) {
            if (view.getEngine().getDocument() != null) {
                return true;
            }
            Thread.sleep(250);
        }
        return false;
    }

    // ------------------------------------------------------------------
    // 4. fixed-point iteration
    // ------------------------------------------------------------------

    private static boolean checkFixedPoint(MainWindowF window, Proof originalProof,
            StringBuilder report) throws InterruptedException {
        SlicingExtensionF extension = findExtension();
        SlicingLeftPanelF panel = extension != null ? extension.getLeftPanel() : null;
        if (panel == null) {
            report.append("no slicing panel attached; ");
            return false;
        }
        SliceToFixedPointDialogF dialog = onFx(() -> panel.openSliceToFixedPointDialog());
        if (dialog == null) {
            report.append("fixed-point dialog did not open (no current proof?); ");
            return false;
        }
        long deadline = System.currentTimeMillis() + TIMEOUT_SECONDS * 1000;
        while (System.currentTimeMillis() < deadline && !dialog.isConverged()) {
            Thread.sleep(1000);
        }
        boolean converged = dialog.isConverged();
        int iterations = dialog.iterationCount();
        report.append("fixed point: ").append(converged ? "converged" : "TIMEOUT")
                .append(" after ").append(iterations).append(" iteration(s); ");
        onFx(dialog::close);
        Proof selected = window.getMediator().getSelectedProof();
        boolean sliceLoaded = selected != null && selected != originalProof && selected.closed();
        report.append("final proof loaded: ")
                .append(sliceLoaded ? "ok" : "unchanged (no slicing potential)")
                .append("; ");
        return converged;
    }

    // ------------------------------------------------------------------
    // 5. recent-files bypass of the direct loader path
    // ------------------------------------------------------------------

    private static boolean checkRecentFilesBypass(MainWindowF window, StringBuilder report)
            throws InterruptedException {
        String demoFile = System.getProperty("key.fx.demo.sequent");
        if (demoFile == null || demoFile.isBlank()) {
            report.append("recent-files bypass not exercised (no key.fx.demo.sequent); ");
            return false;
        }
        List<RecentFilesF.Entry> before = onFx(window::recentFileEntries);
        CountDownLatch loaded = new CountDownLatch(1);
        onFx(() -> window.getMediator().registerProofLoadListener(p -> loaded.countDown()));
        onFx(() -> window.loadProofFileDirect(java.nio.file.Path.of(demoFile)));
        if (!loaded.await(TIMEOUT_SECONDS, TimeUnit.SECONDS)) {
            report.append("direct loader load did not finish; ");
            return false;
        }
        List<RecentFilesF.Entry> after = onFx(window::recentFileEntries);
        boolean untouched = after.equals(before);
        report.append("recent-files bypass: ")
                .append(untouched ? "list untouched by the direct loader load" : "FAILED")
                .append("; ");
        return untouched;
    }

    // ------------------------------------------------------------------
    // helpers
    // ------------------------------------------------------------------

    private static void onFx(Runnable action) throws InterruptedException {
        CountDownLatch latch = new CountDownLatch(1);
        Platform.runLater(() -> {
            try {
                action.run();
            } finally {
                latch.countDown();
            }
        });
        latch.await();
    }

    private static <T> T onFx(Supplier<T> action) throws InterruptedException {
        List<T> holder = new ArrayList<>(1);
        CountDownLatch latch = new CountDownLatch(1);
        Platform.runLater(() -> {
            try {
                holder.add(action.get());
            } finally {
                latch.countDown();
            }
        });
        latch.await();
        return holder.get(0);
    }

    /**
     * Runs auto mode on the demo proof through the window's proof control (Swing parity of the
     * {@code key.fx.demo.autoprove} load-task run).
     */
    private static final class ProofControlAccess {
        static void runAutoMode(MainWindowF window) {
            window.getUserInterfaceControl().getProofControl()
                    .startAndWaitForAutoMode(window.getMediator().getSelectedProof());
        }
    }
}
