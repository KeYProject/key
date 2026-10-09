/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.dialogs;

import java.net.URI;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.nio.charset.StandardCharsets;
import java.time.Duration;
import javafx.geometry.Insets;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar;
import javafx.scene.control.Label;
import javafx.scene.control.TextArea;
import javafx.scene.input.KeyCode;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.VBox;
import javafx.stage.Modality;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF.Kind;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
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
 * header) — the metadata collection is deliberately not ported, {@code // menu:}
 * KNOWN-DEFERRED.</li>
 * <li>Like the Swing original the send is performed off the UI thread
 * ({@code sendReport}, the Swing version blocks the EDT) — here via
 * {@linkplain HttpClient#sendAsync an asynchronous request}; failures surface as error toasts.</li>
 * <li>The Swing "save ZIP to file" alternative (Swing {@code saveZIP}) is not ported (it exists
 * only in the Swing dialog in front of the send step).</li>
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
        Button cancel = new Button("Cancel");
        ButtonBar.setButtonData(send, ButtonBar.ButtonData.OK_DONE);
        ButtonBar.setButtonData(cancel, ButtonBar.ButtonData.CANCEL_CLOSE);
        ButtonBar buttons = new ButtonBar();
        buttons.getButtons().addAll(send, cancel);

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
        cancel.setOnAction(e -> dialog.close());
        dialog.showAndWait();
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
