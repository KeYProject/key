/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension.contrib;

import java.util.List;
import javafx.scene.control.Button;
import javafx.scene.control.Control;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.Tooltip;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

import org.jspecify.annotations.NullMarked;

/**
 * Port of the Swing {@code TestExtension} (key.ui {@code gui.extension.impl.TestExtension},
 * TestExtension.java:35-138) — "should only be used for testing of the extension facade".
 * The Swing original contributes a "Test" action to every extension slot and a main menu at
 * the {@code PATH} {@code "Test.Test.Test"} (TestExtension.java:104-112); this port exercises
 * the FX slots that the P4 batch wired: the path-nested main menu (B13), the PROOF_TREE popup
 * contributions (C24), the merged extension toolbar (B14) and the SEQUENT_VIEW keyboard
 * shortcut seam (D36). Like the Swing original it is registered in the production service
 * file, priority 100000 so it sorts last.
 */
@KeYGuiExtensionF.Info(name = "Test Extension",
    description = "Should only be used for testing of the extension facade", priority = 100000,
    optional = true, experimental = false)
@NullMarked
public final class TestExtensionF implements KeYGuiExtensionF, KeYGuiExtensionF.MainMenuF,
        KeYGuiExtensionF.ContextMenuF, KeYGuiExtensionF.ToolbarF,
        KeYGuiExtensionF.KeyboardShortcutsF {

    /** The "Test" menu item label of the Swing original (TestExtension.java:106). */
    private static final String TEST = "Test";

    /** Shows the Swing original's "Test!" message (a JOptionPane) as an FX toast. */
    private static void showTestMessage() {
        NotificationManagerF.getInstance().notify("Test!");
    }

    private static MenuItem testItem() {
        MenuItem item = new MenuItem(TEST);
        item.setOnAction(e -> showTestMessage());
        return item;
    }

    // --- MainMenuF --------------------------------

    @Override
    public String getMenuPath() {
        // Swing TestExtension.TestAction.setMenuPath("Test.Test.Test"),
        // TestExtension.java:107
        return "Test.Test.Test";
    }

    @Override
    public List<Menu> getMenus(MainWindowF window, KeYMediatorF mediator) {
        Menu menu = new Menu(TEST);
        menu.getItems().add(testItem());
        return List.of(menu);
    }

    // --- ContextMenuF (C24) ------------------------

    @Override
    public List<MenuItem> getSequentContextItems(KeYMediatorF mediator, Goal goal,
            PosInSequent pos) {
        // deliberately empty: the sequent slot is already served by the real extensions; the
        // Test extension only marks the PROOF_TREE slot the P4 batch wired
        return List.of();
    }

    @Override
    public List<MenuItem> getProofTreeContextItems(KeYMediatorF mediator, Node node) {
        // Swing contrib notes the Test action to every context menu kind
        // (TestExtension.java:46-52, 60-63)
        return List.of(testItem());
    }

    // --- ToolbarF (B14) ----------------------------

    @Override
    public List<Control> getToolbarControls(MainWindowF window, KeYMediatorF mediator) {
        Button button = new Button(null, IconFactoryF.createIcon(IconFactoryF.Key.INFO_VIEW));
        button.setTooltip(new Tooltip(TEST));
        button.setOnAction(e -> showTestMessage());
        return List.of(button);
    }

    // --- KeyboardShortcutsF (D36) ------------------

    @Override
    public List<ShortcutF> getShortcuts(KeYMediatorF mediator, String componentId) {
        if (SEQUENT_VIEW.equals(componentId)) {
            // deliberately unbound by the built-in action table: Ctrl+Shift+F12
            return List.of(new ShortcutF(SEQUENT_VIEW,
                new KeyCodeCombination(KeyCode.F12, KeyCombination.CONTROL_DOWN,
                    KeyCombination.SHIFT_DOWN),
                TestExtensionF::showTestMessage));
        }
        return List.of();
    }
}
