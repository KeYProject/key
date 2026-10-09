/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.soundiness;

import java.util.Map;
import javafx.scene.control.Alert;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar;
import javafx.scene.input.Clipboard;
import javafx.scene.input.DataFormat;
import javafx.scene.web.WebView;
import javafx.stage.Modality;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.proof.Proof;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Modal dialog displaying a soundiness report as HTML for a proof.
 * <p>
 * FX port of the Swing {@code de.uka.ilkd.key.gui.soundiness.SoundinessDialog} ({@code key.ui}):
 * a modal window titled {@code "Soundiness Report: <proof>"} ({@code SoundinessDialog.java:27-28})
 * that renders {@link SoundinessAnalyzer#generateHTMLReport(Proof)} in a non-editable HTML view
 * (there a {@code JEditorPane}, here a {@link WebView} — the Swing control renders only a small
 * HTML subset, the WebView renders the report faithfully), with a <em>Copy HTML</em> button
 * writing the raw HTML to the system clipboard plus a confirmation dialog ({@code
 * SoundinessDialog.java:62-69}) and a <em>Close</em> button as the default button ({@code
 * :74-76}). The window is 900×750 and centered on the owner ({@code :53-55}).
 * <p>
 * The report computation lives entirely in {@link SoundinessAnalyzer} (like Swing); the dialog is
 * only the display. Triggered by the "Show Soundiness Report" action (Swing {@code
 * ShowSoundinessAction} contributed to the proof-list context menu by {@code
 * SoundinessExtension}; the FX proof-list dockable does not exist yet, so the action temporarily
 * lives in the View menu — see {@code MainWindowF}).
 */
public final class SoundinessDialogF extends javafx.stage.Stage {

    private static final Logger LOGGER = LoggerFactory.getLogger(SoundinessDialogF.class);

    /**
     * The owner window, kept for centering in {@link #showCenteredOnOwner()} (centering must
     * happen after {@link #show()}, when the stage has its final size).
     */
    private final Window owner;

    /**
     * Creates and shows the soundiness report dialog for the given proof (Swing
     * {@code SoundinessDialog(Frame, Proof)} + {@code setVisible(true)}).
     *
     * @param owner the owner window (the main window stage)
     * @param proof the proof to analyze, non-null
     */
    public SoundinessDialogF(Window owner, Proof proof) {
        setTitle("Soundiness Report: " + proof.name());
        if (owner != null) {
            initOwner(owner);
            // Swing: JDialog(owner, title, true) — modal to the owner window
            initModality(Modality.WINDOW_MODAL);
        }
        String html = SoundinessAnalyzer.generateHTMLReport(proof);

        // the report rendered in a non-editable HTML view (Swing JEditorPane in a scroll pane)
        WebView view = new WebView();
        view.getEngine().loadContent(html, "text/html");

        Button copyButton = new Button("Copy HTML");
        copyButton.setOnAction(e -> {
            // Swing: Toolkit...getSystemClipboard().setContents(new StringSelection(html), null)
            Clipboard.getSystemClipboard()
                    .setContent(Map.of(DataFormat.PLAIN_TEXT, html));
            LOGGER.info("Soundiness report HTML copied to clipboard ({} chars)", html.length());
            Alert info = new Alert(Alert.AlertType.INFORMATION, "HTML copied to clipboard");
            info.setTitle("Copy");
            info.setHeaderText(null);
            if (owner != null) {
                info.initOwner(owner);
            }
            info.getDialogPane()
                    .getStylesheets()
                    .add(ThemeManager.getInstance().getTheme().stylesheetUrl());
            info.showAndWait();
        });

        // Swing: Close is the default button and disposes the dialog
        Button closeButton = new Button("Close");
        closeButton.setOnAction(e -> close());
        ButtonBar.setButtonData(closeButton, ButtonBar.ButtonData.OK_DONE);
        closeButton.setDefaultButton(true);

        ButtonBar buttonBar = new ButtonBar();
        buttonBar.getButtons().addAll(copyButton, closeButton);
        javafx.scene.layout.BorderPane.setMargin(buttonBar, new javafx.geometry.Insets(10));

        javafx.scene.layout.BorderPane root =
            new javafx.scene.layout.BorderPane(view, null, null, buttonBar, null);
        javafx.scene.Scene scene = new javafx.scene.Scene(root, 900, 750);
        ThemeManager.getInstance().manage(scene);
        setScene(scene);
        // Escape closes like the Swing window-close handler (JDialog.DISPOSE_ON_CLOSE)
        scene.setOnKeyPressed(e -> {
            if (e.getCode() == javafx.scene.input.KeyCode.ESCAPE) {
                close();
                e.consume();
            }
        });

        // Swing: pack(); setSize(900, 750); setLocationRelativeTo(getOwner()) — the FX centering
        // happens in showCenteredOnOwner after show(), when the sizes are known
        sizeToScene();
        this.owner = owner;
    }

    /**
     * Centers the dialog over the owner window (Swing {@code setLocationRelativeTo(getOwner())});
     * without an owner, centers on the primary screen. The position is clamped to the screen
     * bounds (the Swing dialog is placed fully on screen as well).
     */
    private void centerOnOwner(Window owner) {
        javafx.geometry.Rectangle2D bounds =
            javafx.stage.Screen.getPrimary().getVisualBounds();
        double x;
        double y;
        if (owner != null && owner.getWidth() > 0) {
            x = owner.getX() + owner.getWidth() / 2 - getWidth() / 2.0;
            y = owner.getY() + owner.getHeight() / 2 - getHeight() / 2.0;
        } else {
            x = bounds.getMinX() + (bounds.getWidth() - getWidth()) / 2;
            y = bounds.getMinY() + (bounds.getHeight() - getHeight()) / 2;
        }
        // clamp into the screen
        setX(Math.max(bounds.getMinX(), Math.min(x, bounds.getMaxX() - getWidth())));
        setY(Math.max(bounds.getMinY(), Math.min(y, bounds.getMaxY() - getHeight())));
    }

    /**
     * Opens the dialog modally (Swing {@code dialog.setVisible(true)} on a modal {@code JDialog};
     * on the FX thread the dialog is non-blocking for the caller) and centers it on the owner.
     */
    public void showCenteredOnOwner() {
        show();
        // Swing setLocationRelativeTo happens on the visible dialog: the sizes are final here
        centerOnOwner(owner);
        toFront();
    }
}
