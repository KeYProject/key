/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.smt;

import javax.swing.JMenuItem;

import de.uka.ilkd.key.smt.SolverTypeCollection;

public class SMTMenuItem extends JMenuItem {
    private static final long serialVersionUID = 1L;
    private final SolverTypeCollection solverUnion;

    public SMTMenuItem(SolverTypeCollection solverUnion) {
        super();
        this.solverUnion = solverUnion;
        this.setText(solverUnion.toString());
    }

    public SolverTypeCollection getSolverUnion() {
        return solverUnion;
    }

    public String toString() {
        return solverUnion.toString();
    }
}
