/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.join;


import javax.swing.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;

import org.key_project.prover.sequent.Sequent;


public class SequentViewer extends JTextPane {

    private static final long serialVersionUID = 1L;


    public SequentViewer() {
        setEditable(false);
        // this.add(new JScrollPane(getTextArea()));



    }


    public void clear() {
        setText("");
    }

    public void setSequent(Sequent sequent, Services services) {
        if (services != null) {
            LogicPrinter printer = LogicPrinter.purePrinter(new NotationInfo(), services);
            printer.printSequent(sequent);
            setText(printer.result());
        }
    }



}
