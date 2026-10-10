/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx;

import java.net.URLDecoder;
import java.nio.charset.StandardCharsets;
import javafx.application.Platform;

import de.uka.ilkd.key.gui.fx.dialogs.FeedbackDialogF;
import de.uka.ilkd.key.gui.fx.docking.Dockable;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF.Kind;
import de.uka.ilkd.key.gui.fx.notification.ProofStatisticsDialogF;
import de.uka.ilkd.key.gui.fx.settings.ToolTipOptionsDialogF;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.util.javafx.FxUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Interactive self test of the {@link WindowUserInterfaceControlF} seam, enabled with the system
 * property {@code key.fx.verify.uicontrol} (the established {@code key.fx.verify.*} pattern of
 * {@code MainWindowF}). Runs after the demo proof load and programmatically fires the seam
 * callbacks:
 * <ol>
 * <li>{@code reportStatus} — asserts that the status bar shows the message;</li>
 * <li>{@code reportException} with a synthetic exception — asserts that an {@link IssueDialogF}
 * is visible with the exception as issue;</li>
 * <li>{@link LogViewF} — opens the log view, emits log lines and asserts that they are
 * rendered;</li>
 * <li>{@link AutoDismissDialogF} — shows the auto-dismiss popup (with an extended delay so it
 * survives until the interactive inspection) and asserts that it is visible;</li>
 * <li>P3c dialogs: the proof-statistics CSV/HTML export (A4), the GitHub issue URL (A6), the
 * feedback ZIP archive (A7), the tooltip "Save as Default" persistence (A8), the separate node
 * buffer (D34) and the status progress bar transitions (D37).</li>
 * </ol>
 * Each step logs a {@code UIControl seam self test: ... PASS/FAIL} line and shows a toast.
 */
public final class UiControlSelfTestF {

    private static final Logger LOGGER = LoggerFactory.getLogger(UiControlSelfTestF.class);

    /** The base of the GitHub new-issue URL (Swing CreateGithubIssueAction.URL). */
    private static final String GITHUB_ISSUE_BASE =
        "https://github.com/keyproject/key/issues/new?body=";

    private UiControlSelfTestF() {
    }

    /** Runs the self test on the given main window (call on the FX thread). */
    public static void run(MainWindowF mainWindow) {
        LOGGER.info("UIControl seam self test: starting");
        WindowUserInterfaceControlF ui = mainWindow.getUserInterfaceControl();

        // 1. status line: reportStatus must update the MainWindowF status bar
        String statusMessage = "Seam self test: status message via reportStatus";
        ui.reportStatus(UiControlSelfTestF.class, statusMessage);
        FxUtil.runLater(() -> {
            String status = mainWindow.getStatusLineText();
            boolean pass = status.contains(statusMessage);
            report("status verification", pass, "status line = '" + status + "'");

            // 2. exception reporting: reportException must open an IssueDialogF. The seam shows
            // a modal showAndWait dialog; headless there is no user to click "OK", so a close is
            // scheduled BEFORE the callback fires — the modal's nested event loop picks the task
            // up and showAndWait returns, letting the verification run right after the dismissal
            Platform.runLater(() -> IssueDialogF.getLastDialog().ifPresent(IssueDialogF::close));
            ui.reportException(UiControlSelfTestF.class, null,
                new IllegalStateException("Seam self test: synthetic exception"));
            FxUtil.runLater(() -> {
                IssueDialogF dialog = IssueDialogF.getLastDialog().orElse(null);
                boolean dialogPass = dialog != null && dialog.wasShown()
                        && dialog.getIssues().stream()
                                .anyMatch(i -> i.text().contains("synthetic exception"));
                report("exception verification", dialogPass,
                    dialog == null ? "no IssueDialogF was opened"
                            : "IssueDialogF wasShown=" + dialog.wasShown() + ", issues="
                                + dialog.getIssues().size());

                // 3. log view: emitted log lines must be rendered by the LogViewF
                LogViewF logView = new LogViewF(LogViewF.resolveLogFile());
                LOGGER.info("Seam self test: log entry A");
                LOGGER.warn("Seam self test: log entry B");
                logView.refresh();
                FxUtil.runLater(() -> {
                    String logReport = logView.verifyContains("Seam self test: log entry A");
                    boolean logPass = logReport.endsWith("PASS");
                    report("log view verification", logPass, logReport);
                    LogViewF.showInstance(mainWindow.getStage());

                    // 4. auto-dismiss popup (extended delay so it survives the inspection; the
                    // countdown code path is identical to the Swing default timings)
                    AutoDismissDialogF autoDismiss = new AutoDismissDialogF(mainWindow.getStage(),
                        "Seam self test: auto-dismiss countdown", 60000, 100, 5000, 5000);
                    autoDismiss.show();
                    FxUtil.runLater(() -> {
                        report("auto dismiss verification", autoDismiss.isVisible(),
                            "AutoDismissDialogF visible=" + autoDismiss.isVisible());

                        runP3cSteps(mainWindow);
                    });
                });
            });
        });
    }

    /** P3c steps 5-10: the A4/A6/A7/A8/D34/D37 seams (call on the FX thread). */
    private static void runP3cSteps(MainWindowF mainWindow) {
        Proof proof = mainWindow.getSelectionModel().getSelectedProof();

        // 5. A4: the proof-statistics CSV/HTML export behind the buttons
        String statsReport = ProofStatisticsDialogF.verifyStatisticsExport(proof);
        report("statistics export verification",
            statsReport.startsWith("PASS") || statsReport.startsWith("SKIP"), statsReport);

        // 6. A6: the GitHub issue URL built by MainWindowF (Swing CreateGithubIssueAction):
        // the body decodes to the bug template with %CHECKSUM% replaced and the Java sources
        String issueUrl = mainWindow.buildGithubIssueUrl();
        String issueBody = URLDecoder.decode(
            issueUrl.substring(issueUrl.indexOf('?') + 1).replaceFirst("^body=", ""),
            StandardCharsets.UTF_8);
        boolean issueOk = issueUrl.startsWith(GITHUB_ISSUE_BASE)
                && issueBody.contains("## Reproducible") && issueBody.contains("* Commit: ")
                && !issueBody.contains("%CHECKSUM%");
        report("github issue url verification", issueOk, "url chars=" + issueUrl.length());

        // 7. A7: the feedback ZIP archive (bug description, version, system properties, logs)
        String archiveReport = FeedbackDialogF.verifyLogArchive();
        report("log archive verification", archiveReport.endsWith("PASS"), archiveReport);

        // 8. A8: "Save as Default" persists the tooltip options into the settings file
        String defaultReport = ToolTipOptionsDialogF.verifySaveAsDefault();
        report("save as default verification", defaultReport.endsWith("PASS"), defaultReport);

        // 9. D34: open a node in a separate sequent buffer, close it again
        if (proof != null) {
            Dockable dock = mainWindow.openNodeInSeparateBuffer(proof.root());
            boolean open = mainWindow.getWorkspace().isOpen(dock.getId());
            boolean titled = dock.getTitle().startsWith("Node: ");
            mainWindow.getWorkspace().close(dock);
            boolean closed = !mainWindow.getWorkspace().isOpen(dock.getId());
            report("node buffer verification", open && titled && closed,
                "open=" + open + " titled=" + titled + " closed=" + closed);
        } else {
            report("node buffer verification", false, "no proof selected");
        }

        // 10. D37: status progress bar visibility/value transitions (Swing MainStatusLine):
        // maximum 0 hides the bar, a positive maximum shows it determinate, a negative maximum
        // switches it to indeterminate ("busy") mode, hideStatusProgress hides it again
        mainWindow.setStatusLine("D37 self test", 0);
        boolean hiddenZero = !mainWindow.isStatusProgressVisible();
        mainWindow.setStatusLine("D37 self test", 100);
        boolean visibleDeterminate = mainWindow.isStatusProgressVisible();
        mainWindow.setTaskProgressValue(50);
        double value = mainWindow.getStatusProgressValue();
        mainWindow.setStatusLine("D37 self test", -1);
        boolean indeterminate = mainWindow.isStatusProgressVisible()
                && mainWindow.getStatusProgressValue() < 0;
        mainWindow.hideStatusProgress();
        boolean hiddenAgain = !mainWindow.isStatusProgressVisible();
        boolean progressOk = hiddenZero && visibleDeterminate && value >= 0.49 && value <= 0.51
                && indeterminate && hiddenAgain;
        report("status progress verification", progressOk,
            "hidden0=" + hiddenZero + " determinate=" + visibleDeterminate + " value=" + value
                + " indeterminate=" + indeterminate + " hiddenAgain=" + hiddenAgain);
    }

    /** Logs the PASS/FAIL result and shows a toast (the established verification pattern). */
    private static void report(String name, boolean pass, String detail) {
        String verdict = pass ? "PASS" : "FAIL";
        LOGGER.info("UIControl seam self test: {} verification: {} ({})", name, verdict, detail);
        NotificationManagerF.getInstance().notify("UIControl seam self test " + name + ": "
            + verdict, pass ? Kind.INFO : Kind.ERROR);
    }
}
