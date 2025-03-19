/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import recoder.java.SourceVisitor;

/**
 * A "\Continue" parameter of a ccatch clause.
 *
 * @author Dominic Steinhöfel
 */
public class CcatchContinueParameterDeclaration extends CcatchNonstandardParameterDeclaration {
    private static final long serialVersionUID = 1L;

    @Override
    public recoder.java.ProgramElement getChildAt(int arg0) {
        return null;
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public int getChildPositionCode(recoder.java.ProgramElement arg0) {
        return 0;
    }

    @Override
    public boolean replaceChild(recoder.java.ProgramElement arg0,
            recoder.java.ProgramElement arg1) {
        return false;
    }

    @Override
    public void accept(SourceVisitor v) {
        if (v instanceof SourceVisitorExtended) {
            ((SourceVisitorExtended) v).visitCcatchContinueParameterDeclaration(this);
        } else {
            // throw new IllegalStateException(
            // "Method 'accept' not implemented in Ccatch");
        }
    }

    @Override
    public CcatchContinueParameterDeclaration deepClone() {
        return new CcatchContinueParameterDeclaration();
    }

}
