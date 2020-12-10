// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.recoderext;

import recoder.java.SourceVisitor;

/**
 * A "\Break" parameter of a ccatch clause.
 *
 * @author Dominic Steinhöfel
 */
public class CcatchBreakParameterDeclaration
        extends CcatchNonstandardParameterDeclaration {
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
            ((SourceVisitorExtended) v)
                    .visitCcatchBreakParameterDeclaration(this);
        } else {
            // throw new IllegalStateException(
            // "Method 'accept' not implemented in Ccatch");
        }
    }

    @Override
    public CcatchBreakParameterDeclaration deepClone() {
        return new CcatchBreakParameterDeclaration();
    }

}
