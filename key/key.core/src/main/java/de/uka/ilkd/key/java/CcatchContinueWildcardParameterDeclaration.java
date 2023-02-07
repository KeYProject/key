/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.java;

import java.io.IOException;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.visitor.Visitor;

/**
 * A "\Continue *" parameter declaration of a ccatch clause.
 *
 * @author Dominic Steinhöfel
 */
public class CcatchContinueWildcardParameterDeclaration
        extends CcatchNonstandardParameterDeclaration {

    public CcatchContinueWildcardParameterDeclaration(ExtList children) {}

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
        v.performActionOnCcatchContinueWildcardParameterDeclaration(this);
    }

    @Override
    public void prettyPrint(PrettyPrinter w) throws IOException {
        w.printCcatchContinueWildcardParameterDeclaration(this);
    }

}
