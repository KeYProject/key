/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx;

import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF.Kind;

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
 * survives until the interactive inspection) and asserts that it is visible.</li>
 * </ol>
 * Each step logs a {@code UIControl seam self test: ... PASS/FAIL} line and shows a toast.
 */
public final class UiControlSelfTestF {

    private static final Logger LOGGER = LoggerFactory.getLogger(UiControlSelfTestF.class);

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

            // 2. exception reporting: reportException must open an IssueDialogF
            ui.reportException(UiControlSelfTestF.class, null,
                new IllegalStateException("Seam self test: synthetic exception"));
            FxUtil.runLater(() -> {
                IssueDialogF dialog = IssueDialogF.getLastDialog().orElse(null);
                boolean dialogPass = dialog != null && dialog.isVisible()
                        && dialog.getIssues().stream()
                                .anyMatch(i -> i.text().contains("synthetic exception"));
                report("exception verification", dialogPass,
                    dialog == null ? "no IssueDialogF was opened"
                            : "IssueDialogF visible=" + dialog.isVisible() + ", issues="
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
                    FxUtil.runLater(() -> report("auto dismiss verification",
                        autoDismiss.isVisible(), "AutoDismissDialogF visible="
                            + autoDismiss.isVisible()));
                });
            });
        });
    }

    /** Logs the PASS/FAIL result and shows a toast (the established verification pattern). */
    private static void report(String name, boolean pass, String detail) {
        String verdict = pass ? "PASS" : "FAIL";
        LOGGER.info("UIControl seam self test: {} verification: {} ({})", name, verdict, detail);
        NotificationManagerF.getInstance().notify("UIControl seam self test " + name + ": "
            + verdict, pass ? Kind.INFO : Kind.ERROR);
    }
}
