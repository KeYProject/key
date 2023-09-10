/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import recoder.java.JavaNonTerminalProgramElement;
import recoder.java.ParameterContainer;

/**
 * A "non-standard" parameter declaration of a Ccatch clause, e.g., "\Return".
 *
 * @author Dominic Steinhöfel
 */
public abstract class CcatchNonstandardParameterDeclaration extends JavaNonTerminalProgramElement {
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
