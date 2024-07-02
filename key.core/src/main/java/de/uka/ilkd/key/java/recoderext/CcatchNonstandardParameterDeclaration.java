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

import recoder.java.JavaNonTerminalProgramElement;
import recoder.java.ParameterContainer;

/**
 * A "non-standard" parameter declaration of a Ccatch clause, e.g., "\Return".
 *
 * @author Dominic Steinhöfel
 */
public abstract class CcatchNonstandardParameterDeclaration
        extends JavaNonTerminalProgramElement {
    private static final long serialVersionUID = 1L;

    private ParameterContainer parent;

    @Override
    public ParameterContainer getASTParent() {
        return parent;
    }

    public ParameterContainer getParameterContainer() {
        return parent;
    }

    public void setParameterContainer(ParameterContainer c) {
        parent = c;
    }

    @Override
    public abstract CcatchNonstandardParameterDeclaration deepClone();
}
