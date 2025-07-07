/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.logic.op.JOperatorSV;

import recoder.java.Identifier;
import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.Statement;
import recoder.java.statement.Catch;

public class CatchSVWrapper extends Catch implements KeYRecoderExtension, SVWrapper {

    /**
     *
     */
    private static final long serialVersionUID = 6288254708744002494L;
    protected final JOperatorSV sv;

    public CatchSVWrapper(JOperatorSV sv) {
        this.sv = sv;
    }


    /**
     * returns a String name of this meta construct.
     */
    public JOperatorSV getSV() {
        return sv;
    }

    public void accept(SourceVisitor v) {
        v.visitIdentifier(new Identifier(sv.name().toString()));
    }

    public CatchSVWrapper deepClone() {
        return new CatchSVWrapper(sv);
    }

    public int getChildCount() {
        return 0;
    }

    public ProgramElement getChildAt(int i) {
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement pe) {
        throw new ArrayIndexOutOfBoundsException();
    }

    public boolean replaceChild(ProgramElement p1, ProgramElement p2) {
        return false;
    }

    public int getStatementCount() {
        return 0;
    }

    public Statement getStatementAt(int s) {
        throw new ArrayIndexOutOfBoundsException();
    }


}
