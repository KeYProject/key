/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.statement.Break;
import de.uka.ilkd.key.logic.op.ProgramVariable;

class BreakToBeReplaced {

    private final Break brk;
    private ProgramVariable pvar;

    public BreakToBeReplaced(Break brk, ProgramVariable pvar) {
        this.brk = brk;
        this.pvar = pvar;
    }

    public BreakToBeReplaced(Break brk) {
        this.brk = brk;
        this.pvar = null;
    }

    Break getBreak() {
        return brk;
    }

    ProgramVariable getProgramVariable() {
        return pvar;
    }

    void setProgramVariable(ProgramVariable pvar) {
        this.pvar = pvar;
    }

}
