/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.jspecify.annotations.NullMarked;

import static de.uka.ilkd.key.settings.ViewSettings.SYNTAX_HIGHLIGHTING;

@NullMarked
public class SyntaxHighlightingToggleAction extends MainWindowAction {
    private static final long serialVersionUID = 6987252955535709994L;

    /**
     * Listens for changes on {@code ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()}.
     *
     * The bound method reference binds {@code this} while the receiver is still under
     * initialization (EISOP initialization check); safe here since the listener only ever fires
     * after construction completes, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:methodref.receiver.bound.invalid")
    private final PropertyChangeListener syntaxHighlightingListener =
        this::handleViewSettingsChanged;

    /**
     * The action-configuration calls and the listener registration below operate on {@code this}
     * while the receiver is still under initialization (EISOP initialization check); safe here
     * since these configure the local action only, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public SyntaxHighlightingToggleAction(MainWindow window) {
        super(window);
        setName("Use Syntax Highlighting");
        setTooltip("Uses regular expressions-based syntax highlighting. "
            + "This helps to understand sequents, but may "
            + "slow down the rendering of longer ones.");
        final boolean useSyntaxHighlighting =
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUseSyntaxHighlighting();
        // Attention: The listener is never
        // removed, because there is only one
        // MainWindow!
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .addPropertyChangeListener(SYNTAX_HIGHLIGHTING, syntaxHighlightingListener);
        setSelected(useSyntaxHighlighting);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean useSyntaxHighlighting = ((JCheckBoxMenuItem) e.getSource()).isSelected();
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .setUseSyntaxHighlighting(useSyntaxHighlighting);
        setSelected(useSyntaxHighlighting);
    }

    protected void handleViewSettingsChanged(PropertyChangeEvent e) {
        mainWindow.makePrettyView();
    }
}
