/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension.contrib;

import java.util.List;
import javafx.scene.control.Button;
import javafx.scene.control.Control;
import javafx.scene.control.Tooltip;

import de.uka.ilkd.key.gui.fx.LogViewF;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.gui.fx.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The log-view extension, FX port of the Swing {@code de.uka.ilkd.key.gui.LogView} (Swing
 * LogView.java:33-126): the Swing original is both the extension and the view — it implements
 * {@code KeYGuiExtension.StatusLine} and contributes a single status-line button that opens
 * the log window ({@code getStatusLineComponents}, LogView.java:47-52, a {@code JButton} for
 * the {@code ShowLogAction} whose {@code actionPerformed} creates the non-modal log dialog,
 * LogView.java:94-125).
 * <p>
 * The view itself (the Swing {@code ShowLogAction} dialog with the {@code LogViewPane} and the
 * {@code FileWatcherService} + {@code OpenLogExternalAction}, LogView.java:54-324) is already
 * ported as {@link LogViewF}; this provider ports the remaining extension surface: the
 * status-line button with the Swing BOOK icon at size 16 and the "Show log" tooltip (Swing
 * {@code ShowLogAction} constructor, LogView.java:88-92). The Swing {@code JButton} of the
 * name-less {@code ShowLogAction} renders icon-only (the action never sets a {@code NAME}), so
 * the FX button is icon-only as well. Its action opens the very same {@link LogViewF} window
 * the View-menu entry opens ({@code MainWindowF} "Log View" item → {@code showLogView} →
 * {@code LogViewF.showInstance}, the Swing-parity status-line seam already noted there); the
 * open is single-instance, so the two entry points share one window (the KNOWN-SIMPLIFIED
 * marker on {@code LogViewF.showInstance}).
 * <p>
 * The provider is instantiable without a running JavaFX toolkit: the button is created lazily
 * in {@link #getStatusLineControls()} (JavaFX 25 throws "Toolkit not initialized" when a
 * control is constructed headless; the CachingExtensionF lazily-created convention).
 */
@KeYGuiExtensionF.Info(experimental = false, name = "Log View")
@NullMarked
public final class LogViewExtensionF implements KeYGuiExtensionF, KeYGuiExtensionF.StatusLineF {

    private static final Logger LOGGER = LoggerFactory.getLogger(LogViewExtensionF.class);

    /**
     * The status-line button (Swing {@code btnShowLog}, LogView.java:49-51), created lazily by
     * {@link #getStatusLineControls()} — never in the constructor or a field initializer, so
     * the provider stays instantiable headless.
     */
    private @Nullable Button button;

    @Override
    public List<Control> getStatusLineControls() {
        Button btn = button;
        if (btn == null) {
            btn = new Button();
            // Swing ShowLogAction constructor (LogView.java:88-92): the BOOK icon at size 16
            // (IconFontProvider(FontAwesomeSolid.BOOK) + setIcon(BOOK.get(16))) and the tooltip
            // "Show log"; no action NAME is set, so the Swing button shows the icon only
            btn.setGraphic(IconFactoryF.createIcon(FontAwesomeSolid.BOOK, 16));
            btn.setTooltip(new Tooltip("Show log"));
            // Swing ShowLogAction.actionPerformed (LogView.java:94-125): opens the log view
            // window. The FX open goes through the shared LogViewF.showInstance seam that the
            // View-menu entry uses as well (MainWindowF.showLogView), so both entry points
            // open the same (single-instance) log view window; the owner is the main window
            // stage like the View-menu open, null-safe when no window exists yet
            btn.setOnAction(e -> {
                LOGGER.debug("Status-line button: opening the log view window");
                MainWindowF window = MainWindowF.getInstance();
                LogViewF.showInstance(window != null ? window.getStage() : null);
            });
            button = btn;
        }
        return List.of(btn);
    }
}
