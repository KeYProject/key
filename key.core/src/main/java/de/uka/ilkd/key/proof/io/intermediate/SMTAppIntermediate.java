/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io.intermediate;

import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.util.Pair;

public class SMTAppIntermediate extends BuiltInAppIntermediate {
    private final String solver;

    public SMTAppIntermediate(String ruleName, Pair<Integer, PosInTerm> pos, String solver) {
        super(ruleName, pos, null, null, null, null);
        this.solver = solver;
    }

    public String getSolver() {
        return solver;
    }
}
