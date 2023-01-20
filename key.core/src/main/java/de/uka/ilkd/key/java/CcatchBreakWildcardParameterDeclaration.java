/*
 * This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0
 */
package de.uka.ilkd.key.java;

import java.io.IOException;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.visitor.Visitor;

/**
 * A "\Break *" parameter declaration of a ccatch clause.
 *
 * @author Dominic Steinhöfel
 */
public class CcatchBreakWildcardParameterDeclaration extends CcatchNonstandardParameterDeclaration {

    public CcatchBreakWildcardParameterDeclaration(ExtList children) {}

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        return null;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnCcatchBreakWildcardParameterDeclaration(this);
    }

    @Override
    public void prettyPrint(PrettyPrinter w) throws IOException {
        w.printCcatchBreakWildcardParameterDeclaration(this);
    }

}
