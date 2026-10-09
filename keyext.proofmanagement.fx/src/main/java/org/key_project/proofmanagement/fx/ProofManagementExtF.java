/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.proofmanagement.fx;

import java.util.List;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;
import javafx.stage.Window;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * The proof management extension, FX port of {@code org.key_project.proofmanagement.
 * ProofManagementExt} (Swing ProofManagementExt.java:18-91): a "Proof Management" menu with the
 * single active action "Check proof bundle ..." (Swing {@code CheckAction}) that opens the
 * check-configuration dialog and runs the soundness checks on a proof bundle.
 * <p>
 * Port notes and deviations from the Swing original:
 * <ul>
 * <li>The Swing provider implements only {@code KeYGuiExtension.MainMenu} (ProofManagementExt.
 * java:27-28); the FX port implements the {@link KeYGuiExtensionF.MainMenuF} counterpart and
 * nothing else — no other capability slot exists in the original.</li>
 * <li>The FX SPI contributes whole {@link Menu}s that the host appends to the menu bar as new
 * separate menus after the five built-in menus (the Swing facade grouped the extension actions
 * into one "Extensions" JMenu). The "Proof Management" menu is a SIXTH menu; the five built-in
 * menus and their item sets stay untouched ({@code key.fx.verify.menuparity}).</li>
 * <li>Only the ACTIVE action (the {@code CheckAction}) is ported: the Merge/Bundle actions are
 * commented out in the Swing original (ProofManagementExt.java:54-84) and are deliberately not
 * ported.</li>
 * <li>The check action is <em>proof-bundle based</em> (it checks a proof bundle on disk, not
 * the currently loaded proof), so the provider neither reads nor requires the open proof: menu
 * construction is proof-independent and the exclusive failure guard is the empty-bundle-path
 * validation of the dialog (mirroring the Swing {@code CheckConfigDialog} run handler).</li>
 * <li>The check configuration dialog is ported in pure JavaFX in {@link CheckConfigDialogF} —
 * {@code org.key_project.proofmanagement.Main.CheckCommand} (the actual check orchestration,
 * report generation included) is reused unchanged.</li>
 * </ul>
 */
@KeYGuiExtensionF.Info(name = "Proof management", optional = true,
    description = "Allows to run soundness checks on proof bundles.", experimental = false)
@NullMarked
public class ProofManagementExtF implements KeYGuiExtensionF, KeYGuiExtensionF.MainMenuF {

    /** The text of the contributed menu (Swing ProofManagementExt.MENU_PM). */
    private static final String MENU_PM = "Proof Management";

    @Override
    public List<Menu> getMenus(MainWindowF window, KeYMediatorF mediator) {
        // extension: MP9.6 — Swing ProofManagementExt.getMainMenuActions (ProofManagementExt.
        // java:32-36): the menu holds the check action; the FX SPI contributes whole menus, so
        // the action lives in a NEW separate "Proof Management" menu. The mediator is unused:
        // the action is proof-bundle based and needs no open proof.
        return List.of(buildMenu(window));
    }

    /**
     * Builds the "Proof Management" menu with the "Check proof bundle ..." action that opens the
     * check-configuration dialog ({@link CheckConfigDialogF}), parented to the given window's
     * stage when available (Swing passed {@code MainWindow.getInstance()} as dialog owner,
     * ProofManagementExt.java:47-50).
     *
     * @param window the main window, or {@code null} (tests / detached usage) — the dialog is
     *        opened unparented then
     * @return the non-null menu
     */
    static Menu buildMenu(@Nullable MainWindowF window) {
        Menu menu = new Menu(MENU_PM);
        MenuItem check = new MenuItem("Check proof bundle ...");
        check.setOnAction(e -> {
            Window owner = window == null ? null : window.getStage();
            new CheckConfigDialogF(owner).showAndWait();
        });
        menu.getItems().add(check);
        return menu;
    }
}
