/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.join;

import javafx.scene.control.TextArea;
import javafx.scene.text.Font;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;

import org.key_project.prover.sequent.Sequent;

/**
 * Read-only embedded sequent renderer used to show partner sequents inside the join dialog.
 * <p>
 * Port of the Swing {@code de.uka.ilkd.key.gui.join.SequentViewer} (key.ui), a non-editable
 * JTextPane fed by {@code LogicPrinter.purePrinter}: the FX port is a non-editable monospaced
 * {@link TextArea} fed by the same printer.
 *
 * @author Benjamin Niedermann (original Swing component)
 */
public class SequentViewerF extends TextArea {

    public SequentViewerF() {
        setEditable(false);
        setFont(Font.font("Monospaced", 13));
        getStyleClass().add("join-sequent-view");
    }

    public void clear() {
        setText("");
    }

    /**
     * Prints the given sequent into the viewer (Swing {@code setSequent}).
     *
     * @param sequent the sequent to print
     * @param services the services used for pretty printing
     */
    public void setSequent(Sequent sequent, Services services) {
        if (services != null) {
            LogicPrinter printer = LogicPrinter.purePrinter(new NotationInfo(), services);
            printer.printSequent(sequent);
            setText(printer.result());
        }
    }
}
