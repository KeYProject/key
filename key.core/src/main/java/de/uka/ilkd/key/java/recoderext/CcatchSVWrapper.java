/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.logic.op.JOperatorSV;

import recoder.java.Identifier;
import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.Statement;

public class CcatchSVWrapper extends Ccatch implements KeYRecoderExtension, SVWrapper {
    private static final long serialVersionUID = -1;
    protected final JOperatorSV sv;

    public CcatchSVWrapper(JOperatorSV sv) {
        this.sv = sv;
    }

    /**
     * returns a String name of this meta construct.
     */
    @Override
    public JOperatorSV getSV() {
        return sv;
    }

    @Override
    public void accept(SourceVisitor v) {
        v.visitIdentifier(new Identifier(sv.name().toString()));
    }

    @Override
    public CcatchSVWrapper deepClone() {
        return new CcatchSVWrapper(sv);
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public ProgramElement getChildAt(int i) {
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public int getChildPositionCode(ProgramElement pe) {
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public boolean replaceChild(ProgramElement p1, ProgramElement p2) {
        return false;
    }

    @Override
    public int getStatementCount() {
        return 0;
    }

    @Override
    public Statement getStatementAt(int s) {
        throw new ArrayIndexOutOfBoundsException();
    }

}
