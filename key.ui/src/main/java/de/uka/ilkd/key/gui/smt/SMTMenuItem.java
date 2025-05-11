/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.smt;

import javax.swing.JMenuItem;

import de.uka.ilkd.key.smt.SolverTypeCollection;

import org.jspecify.annotations.NonNull;

public class SMTMenuItem extends JMenuItem {
    private static final long serialVersionUID = 1L;
    private final @NonNull SolverTypeCollection solverUnion;

    public SMTMenuItem(@NonNull SolverTypeCollection solverUnion) {
        super();
        this.solverUnion = solverUnion;
        this.setText(solverUnion.toString());
    }

    public @NonNull SolverTypeCollection getSolverUnion() {
        return solverUnion;
    }

    public @NonNull String toString() {
        return solverUnion.toString();
    }
}
