/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.join;

import javax.swing.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;

import org.key_project.prover.sequent.Sequent;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public class SequentViewer extends JTextPane {

    private static final long serialVersionUID = 1L;

    /**
     * Creates the sequent viewer.
     *
     * <p>
     * The viewer makes itself read-only while the receiver is still under initialization (EISOP
     * initialization check); the editable state only materializes once the viewer is displayed
     * after construction, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public SequentViewer() {
        setEditable(false);
        // this.add(new JScrollPane(getTextArea()));

    }

    public void clear() {
        setText("");
    }

    public void setSequent(Sequent sequent, @Nullable Services services) {
        if (services != null) {
            LogicPrinter printer = LogicPrinter.purePrinter(new NotationInfo(), services);
            printer.printSequent(sequent);
            setText(printer.result());
        }
    }

}
