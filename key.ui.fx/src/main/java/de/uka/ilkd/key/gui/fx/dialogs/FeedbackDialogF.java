/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.dialogs;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.net.URI;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;
import javafx.geometry.Insets;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar;
import javafx.scene.control.Label;
import javafx.scene.control.TextArea;
import javafx.scene.input.KeyCode;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.VBox;
import javafx.stage.FileChooser;
import javafx.stage.Modality;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF.Kind;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.KeYResourceManager;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * menu: MP5 — minimal JavaFX port of the Swing {@code SendFeedbackAction} dialog
 * (key.ui/.../gui/actions/SendFeedbackAction.java), opened by the About&gt;Send Feedback… entry
 * (Swing {@code MenuSendFeedackAction}). The user writes a description which is then sent to the
 * KeY report server.
 * <p>
 * Port notes and deviations from the Swing original:
 * <ul>
 * <li>The Swing dialog collects a whole <em>metadata zip</em> (proof, last problem, settings,
 * version, system properties, … {@code saveMetaData}) and sends it as
 * {@code Content-Type: application/zip} after an "Ready to send?" confirmation; this port sends
 * the bare description as {@code text/plain; charset=UTF-8} (with the same {@code KeY-Version}
 * header) — the metadata collection is deliberately not ported for the send path,
 * {@code // menu:} KNOWN-DEFERRED.</li>
 * <li>Like the Swing original the send is performed off the UI thread
 * ({@code sendReport}, the Swing version blocks the EDT) — here via
 * {@linkplain HttpClient#sendAsync an asynchronous request}; failures surface as error toasts.</li>
 * <li>The Swing "save ZIP to file" alternative (Swing {@code saveZIP}) is ported as the
 * "Save ZIP…" button (A7, P3c): the archive holds the bug description, the KeY version, the
 * system properties and the {@code key_*.log} log files of the current run — the portable
 * subset of the Swing metadata items (no proof/settings/goal payload, documented in
 * {@link #writeLogArchive}).</li>
 * </ul>
 */
public final class FeedbackDialogF {
    private static final Logger LOGGER = LoggerFactory.getLogger(FeedbackDialogF.class);

    /**
     * The url to which the feedback will be sent (Swing {@code SendFeedbackAction.REPORT_URL}).
     */
    public static final String REPORT_URL = "https://formal.kastel.kit.edu/key/key-report.php";

    /** The email address the report is forwarded to (Swing {@code FEEDBACK_RECIPIENT}). */
    public static final String FEEDBACK_RECIPIENT = "support@key-project.org";

    private FeedbackDialogF() {
    }

    /**
     * Shows the modal feedback dialog and sends the entered description to {@link #REPORT_URL}.
     *
     * @param owner the owner window (the main window stage), may be {@code null}
     */
    public static void show(Window owner) {
        javafx.stage.Stage dialog = new javafx.stage.Stage();
        dialog.setTitle("Report an error to KeY developers");
        dialog.initOwner(owner);
        if (owner != null) {
            // Swing: JDialog(parent, title, DOCUMENT_MODAL)
            dialog.initModality(Modality.WINDOW_MODAL);
        }

        Label hint = new Label("Describe the problem you encountered. The report is sent to "
            + "https://formal.kastel.kit.edu/key/key-report.php and forwarded to the KeY "
            + "mailing list <" + FEEDBACK_RECIPIENT + ">.");
        hint.setWrapText(true);

        TextArea message = new TextArea();
        message.setPromptText("Your feedback…");
        message.setWrapText(true);
        VBox.setVgrow(message, javafx.scene.layout.Priority.ALWAYS);

        Button send = new Button("Send");
        send.setDefaultButton(true);
        // A7 (P3c): the Swing "Save Feedback..." alternative (SendFeedbackAction.saveZIP) as a
        // second action in the button bar — the archive is written via {@link #writeLogArchive}.
        Button saveZip = new Button("Save ZIP…");
        saveZip.setTooltip(new javafx.scene.control.Tooltip(
            "Information about the current run are saved to a zip file. "
                + "This file can be also used when reporting a bug via e-mail."));
        Button cancel = new Button("Cancel");
        ButtonBar.setButtonData(send, ButtonBar.ButtonData.OK_DONE);
        ButtonBar.setButtonData(cancel, ButtonBar.ButtonData.CANCEL_CLOSE);
        ButtonBar.setButtonData(saveZip, ButtonBar.ButtonData.LEFT);
        ButtonBar buttons = new ButtonBar();
        buttons.getButtons().addAll(send, saveZip, cancel);

        VBox center = new VBox(10, hint, message);
        center.setPadding(new Insets(12));
        BorderPane root = new BorderPane();
        root.setCenter(center);
        root.setBottom(buttons);
        BorderPane.setMargin(buttons, new Insets(10));
        Scene scene = new Scene(root, 560, 300);
        ThemeManager.getInstance().manage(scene);
        scene.setOnKeyPressed(e -> {
            if (e.getCode() == KeyCode.ESCAPE) {
                dialog.close();
                e.consume();
            }
        });
        dialog.setScene(scene);

        send.setOnAction(e -> {
            send.setDisable(true);
            dialog.close();
            sendReport(owner, message.getText());
        });
        saveZip.setOnAction(e -> {
            saveZipToFile(owner, message.getText());
            dialog.close(); // Swing: saveZIP(...) then dispose()
        });
        cancel.setOnAction(e -> dialog.close());
        dialog.showAndWait();
    }

    /**
     * A7 (P3c): saves the feedback together with run metadata as a ZIP archive, chosen through a
     * save dialog (Swing {@code SendFeedbackAction.saveZIP} + the "Save Feedback..." button).
     * On success an INFO toast with the target file is shown (Swing
     * {@code JOptionPane.showMessageDialog}; the FX port follows the toast convention).
     */
    private static void saveZipToFile(Window owner, String message) {
        try {
            FileChooser chooser = new FileChooser();
            chooser.setTitle("Save Feedback");
            chooser.setInitialFileName("key-feedback.zip");
            chooser.getExtensionFilters().add(
                new FileChooser.ExtensionFilter("ZIP archives", "*.zip"));
            File file = chooser.showSaveDialog(owner);
            if (file == null) {
                return; // dialog cancelled
            }
            writeLogArchive(file.toPath(), message);
            LOGGER.info("Feedback archive written to {}", file);
            NotificationManagerF.getInstance().notify(
                "Your message has been saved to the file " + file.getAbsolutePath() + ".\n"
                    + "If you want to report a bug, you can enclose this file in an e-mail to "
                    + FEEDBACK_RECIPIENT + ".",
                Kind.INFO);
        } catch (IOException e) {
            LOGGER.error("Saving the feedback archive failed", e);
            NotificationManagerF.getInstance().notify(
                "Saving the feedback archive failed: " + e.getMessage(), Kind.ERROR);
        }
    }

    /**
     * Writes the feedback ZIP archive (Swing {@code SendFeedbackAction.saveMetaDataToFile} with
     * the portable subset of the {@code items} the FX port collects):
     * <ul>
     * <li>{@code bugDescription.txt} — the entered description (Swing {@code bugDescription.txt}
     * entry),</li>
     * <li>{@code keyVersion.txt} — {@link KeYConstants#VERSION} (Swing {@code VersionItem}),</li>
     * <li>{@code systemProperties.txt} — the JVM system properties in the Swing
     * {@code SystemPropertiesItem} {@code Properties.list} format,</li>
     * <li>the {@code key_*.log} files of the current run from
     * {@link PathConfig#currentPaths}{@code .logDirectory} (the Swing {@code StacktraceItem} /
     * {@code FaultyFileItem} / proof and settings items are {@code // menu:} KNOWN-DEFERRED).</li>
     * </ul>
     * Exposed for the {@code key.fx.verify.uicontrol} self test ({@link #verifyLogArchive}).
     *
     * @param target the ZIP file to write
     * @param message the bug description to store as {@code bugDescription.txt}
     * @throws IOException when the archive cannot be written
     */
    public static void writeLogArchive(Path target, String message) throws IOException {
        try (ZipOutputStream zip =
            new ZipOutputStream(new BufferedOutputStream(new FileOutputStream(target.toFile())))) {
            writeEntry(zip, "bugDescription.txt", message.getBytes(StandardCharsets.UTF_8));
            writeEntry(zip, "keyVersion.txt",
                KeYConstants.VERSION.getBytes(StandardCharsets.UTF_8));
            writeEntry(zip, "systemProperties.txt", systemPropertiesText());
            Path logDir = PathConfig.currentPaths.logDirectory;
            LOGGER.debug("Feedback archive: collecting log files from {}", logDir);
            if (logDir != null && Files.isDirectory(logDir)) {
                try (var logs = Files.list(logDir)) {
                    for (Path log : logs.filter(p -> p.getFileName().toString().startsWith("key_")
                            && p.getFileName().toString().endsWith(".log")).toList()) {
                        LOGGER.debug("Feedback archive: adding log file {}", log);
                        writeEntry(zip, log.getFileName().toString(), Files.readAllBytes(log));
                    }
                }
            }
        }
    }

    /** Writes one entry with the given name and content to the ZIP stream. */
    private static void writeEntry(ZipOutputStream zip, String name, byte[] content)
            throws IOException {
        zip.putNextEntry(new ZipEntry(name));
        zip.write(content);
        zip.closeEntry();
    }

    /**
     * A7 (P3c): self test of {@link #writeLogArchive} — writes an archive with a fixed message
     * into a temporary directory and checks the expected entries (bug description, version,
     * system properties, {@code key_*.log} files).
     *
     * @return a self-test report ending in {@code PASS} or {@code FAIL}
     */
    public static String verifyLogArchive() {
        try {
            Path dir = Files.createTempDirectory("keyfx-feedback-archive-");
            Path zip = dir.resolve("feedback-test.zip");
            writeLogArchive(zip, "Seam self test: bug description");
            boolean hasDescription = false;
            boolean hasVersion = false;
            boolean hasSystemProperties = false;
            int logEntries = 0;
            try (java.util.zip.ZipFile zf = new java.util.zip.ZipFile(zip.toFile())) {
                var entries = zf.entries();
                while (entries.hasMoreElements()) {
                    String name = entries.nextElement().getName();
                    hasDescription |= name.equals("bugDescription.txt");
                    hasVersion |= name.equals("keyVersion.txt");
                    hasSystemProperties |= name.equals("systemProperties.txt");
                    logEntries += name.startsWith("key_") && name.endsWith(".log") ? 1 : 0;
                }
            }
            boolean pass = hasDescription && hasVersion && hasSystemProperties && logEntries > 0;
            return "entries bugDescription=" + hasDescription + " keyVersion=" + hasVersion
                + " systemProperties=" + hasSystemProperties + " logs=" + logEntries + " "
                + (pass ? "PASS" : "FAIL");
        } catch (IOException e) {
            LOGGER.warn("Log archive self test failed", e);
            return "Feedback archive self test failed: " + e.getMessage() + " FAIL";
        }
    }

    /** The JVM system properties in the Swing {@code Properties.list} line format. */
    private static byte[] systemPropertiesText() {
        StringWriter sw = new StringWriter();
        try (PrintWriter pw = new PrintWriter(sw)) {
            System.getProperties().list(pw);
        }
        return sw.toString().getBytes(StandardCharsets.UTF_8);
    }

    /**
     * Posts the feedback text to the {@linkplain #REPORT_URL report server} (Swing
     * {@code SendFeedbackAction.sendReport}): the {@code http.client} POST carries the same
     * {@code KeY-Version} header as the Swing original; on HTTP 200 the caller gets an info
     * toast, otherwise the response body is reported as an error toast.
     */
    private static void sendReport(Window owner, String text) {
        if (text == null || text.isBlank()) {
            NotificationManagerF.getInstance()
                    .notify("Feedback not sent: the description is empty.", Kind.WARNING);
            return;
        }
        HttpRequest request = HttpRequest.newBuilder(URI.create(REPORT_URL))
                // menu: Swing sends an application/zip metadata bundle (saveMetaData); this port
                // sends the plain description, so the content type differs (KNOWN-DEFERRED above)
                .header("Content-Type", "text/plain; charset=UTF-8")
                .header("KeY-Version", "KeY " + KeYResourceManager.getManager().getVersion())
                .timeout(Duration.ofSeconds(30))
                .POST(HttpRequest.BodyPublishers.ofString(text, StandardCharsets.UTF_8))
                .build();
        HttpClient.newHttpClient().sendAsync(request, HttpResponse.BodyHandlers.ofString())
                .whenComplete((response, error) -> {
                    if (error != null) {
                        LOGGER.error("Sending feedback failed", error);
                        NotificationManagerF.getInstance().notify(
                            "Sending feedback failed: " + error.getMessage(), Kind.ERROR);
                        return;
                    }
                    int code = response.statusCode();
                    if (code == 200) {
                        LOGGER.info("Feedback sent to {}", REPORT_URL);
                        NotificationManagerF.getInstance()
                                .notify("Your report has been filed successfully. Thank you!",
                                    Kind.INFO);
                    } else {
                        String body = response.body();
                        LOGGER.error("Sending feedback failed, server responded {}: {}", code,
                            body);
                        NotificationManagerF.getInstance().notify(
                            "Sending feedback failed, the server responded with " + code + ": "
                                + body,
                            Kind.ERROR);
                    }
                });
    }
}
