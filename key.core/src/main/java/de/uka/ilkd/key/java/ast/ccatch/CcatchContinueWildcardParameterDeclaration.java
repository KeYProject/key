/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.ccatch;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * A "\Continue *" parameter declaration of a ccatch clause.
 *
 * @author Dominic Steinhöfel
 */
public class CcatchContinueWildcardParameterDeclaration
        extends CcatchNonstandardParameterDeclaration {

    public CcatchContinueWildcardParameterDeclaration(ExtList children) {}

    public CcatchContinueWildcardParameterDeclaration(PositionInfo pi, List<Comment> c) {
        super(pi, c);
    }

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

}
