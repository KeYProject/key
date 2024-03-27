/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceData;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.rule.MatchConditions;

public class SwitchBranchSVWrapper extends SwitchBranch {
    private final ProgramSV sv;

    public SwitchBranchSVWrapper(ProgramSV sv) {
        this.sv = sv;
    }

    public ProgramSV getSv() {
        return sv;
    }


    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        throw new IndexOutOfBoundsException();
    }

    @Override
    public void visit(Visitor v) {

    }

    @Override
    public int getStatementCount() {
        return 0;
    }

    @Override
    public Statement getStatementAt(int index) {
        throw new IndexOutOfBoundsException();
    }

    @Override
    public String toString() {
        return sv.toString();
    }

    @Override
    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        return sv.match(source, matchCond);
    }
}
