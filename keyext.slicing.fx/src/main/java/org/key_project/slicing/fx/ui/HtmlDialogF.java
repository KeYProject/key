/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.slicing.fx.ui;

import javafx.geometry.Insets;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar;
import javafx.scene.layout.BorderPane;
import javafx.scene.web.WebView;
import javafx.stage.Modality;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.theme.ThemeManager;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Dialog that displays an HTML document, FX port of {@code org.key_project.slicing.ui.HtmlDialog}
 * (which hosts the HTML in a Swing {@code JEditorPane}): the FX counterpart renders the HTML in
 * a non-editable {@link WebView} above a Close button, the same seam the
 * {@code SoundinessDialogF} report uses for its HTML output. Replaces the read-only multi-line
 * text dialog stand-in for the HTML statistics, the execution timings and the fixed-point
 * progress tables.
 * <p>
 * Deviation from the Swing original: the {@code linkPressedCallback} of the Swing constructor is
 * not ported (none of the current callers passes non-null links — the statistics and timings
 * tables are generated with all columns non-clickable); a follow-up caller needing hyperlink
 * activation can use the {@code WebView} engine's confirm handler.
 */
@NullMarked
public class HtmlDialogF extends javafx.stage.Stage {

    private static final Logger LOGGER = LoggerFactory.getLogger(HtmlDialogF.class);

    /** The rendered HTML content (exposed for the {@code key.fx.verify.slicing} harness). */
    private final WebView webView;

    /**
     * Construct and show a new dialog for the provided HTML (Swing
     * {@code HtmlDialog(Window, String, String, Consumer)}).
     *
     * @param owner owner window, may be {@code null}
     * @param title title of the new dialog
     * @param html HTML to show
     */
    public HtmlDialogF(@Nullable Window owner, String title, String html) {
        setTitle(title);
        if (owner != null) {
            initOwner(owner);
            initModality(Modality.NONE);
        }

        webView = new WebView();
        webView.setPrefSize(760, 420);
        webView.getEngine().loadContent(html, "text/html");

        Button closeButton = new Button("Close");
        closeButton.setOnAction(e -> close());
        ButtonBar.setButtonData(closeButton, ButtonBar.ButtonData.OK_DONE);
        closeButton.setDefaultButton(true);
        ButtonBar buttonBar = new ButtonBar();
        buttonBar.getButtons().add(closeButton);
        BorderPane.setMargin(buttonBar, new Insets(10));

        BorderPane root = new BorderPane(webView, null, null, buttonBar, null);
        Scene scene = new Scene(root, 800, 500);
        try {
            // theme the dialog like the other FX dialogs (best effort)
            scene.getStylesheets().add(ThemeManager.getInstance().getTheme().stylesheetUrl());
        } catch (RuntimeException e) {
            LOGGER.debug("could not theme the HTML dialog", e);
        }
        setScene(scene);
    }

    /** @return the web view showing the HTML (verify harness seam) */
    public WebView getWebView() {
        return webView;
    }

    /**
     * Creates and shows the dialog (Swing {@code new HtmlDialog(...)} + implicit
     * {@code setVisible(true)}).
     *
     * @param owner owner window, may be {@code null}
     * @param title title of the new dialog
     * @param html HTML to show
     * @return the shown dialog
     */
    public static HtmlDialogF show(@Nullable Window owner, String title, String html) {
        HtmlDialogF dialog = new HtmlDialogF(owner, title, html);
        dialog.show();
        return dialog;
    }
}
