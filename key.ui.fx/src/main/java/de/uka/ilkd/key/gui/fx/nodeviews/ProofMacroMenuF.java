/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.nodeviews;

import javafx.scene.control.CustomMenuItem;
import javafx.scene.control.Label;
import javafx.scene.control.MenuItem;
import javafx.scene.control.Tooltip;

import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.gui.fx.keyshortcuts.KeyStrokeManagerF;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Node;

import org.key_project.prover.sequent.PosInOccurrence;

/**
 * menu: MP8 — shared construction of one proof-macro menu item (Swing {@code ProofMacroMenu}
 * createMenuItem, ProofMacroMenu.java:143-144: item text = {@code macro.getName()}, tooltip =
 * {@code macro.getDescription()}). Used by the sequent-view right-click macro popup (MP7,
 * {@link SequentViewF#buildMacroPopup}) and by the term-menu "Strategy Macros" section (MP8b,
 * {@link SequentTermContextMenuF}) so both present the very same macros with the same look.
 * <p>
 * JavaFX {@link MenuItem} has no tooltip property (unlike Swing {@code
 * JMenuItem.setToolTipText}), so the item is a {@link CustomMenuItem} wrapping a
 * tooltip-bearing {@link Label}.
 */
final class ProofMacroMenuF {

    private ProofMacroMenuF() {
    }

    /**
     * menu: MP8 — a single macro item whose action runs the macro on the selected node at the
     * given position (Swing {@code ProofMacroUserAction}, ProofMacroUserAction.java:57-59:
     * {@code mediator.getUI().getProofControl().runMacro(node, macro, pio)}; the core silently
     * ignores the run while auto mode is active, and {@code pio} may be {@code null} — a
     * sequent position may resolve to no occurrence and global macros accept that).
     *
     * @param macro the macro to run
     * @param node the node the macro is started at (the mediator's selection)
     * @param proofControl the proof control to run the macro with
     * @param pio the clicked {@link PosInOccurrence}, possibly {@code null}
     * @return the wired macro menu item
     */
    static MenuItem itemFor(ProofMacro macro, Node node, ProofControl proofControl,
            PosInOccurrence pio) {
        Label label = new Label(macro.getName());
        Tooltip.install(label, new Tooltip(macro.getDescription()));
        CustomMenuItem item = new CustomMenuItem(label);
        item.setOnAction(e -> proofControl.runMacro(node, macro, pio));
        // shortcuts (P1): macro accelerators on the term-menu items for global applications
        // (Swing ProofMacroMenu.createMenuItem, ProofMacroMenu.java:146-148: "currently only
        // for global macro applications")
        if (pio == null) {
            KeyStrokeManagerF.getInstance().binding(macro.getClass().getName())
                    .ifPresent(item::setAccelerator);
        }
        return item;
    }
}
