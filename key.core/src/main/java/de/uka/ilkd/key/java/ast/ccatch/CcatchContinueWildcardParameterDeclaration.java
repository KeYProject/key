/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.ccatch;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * A "\Continue *" parameter declaration of a ccatch clause.
 *
 * @author Dominic Steinhöfel
 */
@NullMarked
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

    // Returns null by design (this clause has no children). The base contract
    // NonTerminalProgramElement.getChildAt(int) is @NonNull and cannot be widened (it ripples into
    // key.ncore SyntaxElement.getChild(int) + ~40 overrides; wave-7 SuperArrayDeclaration
    // precedent), so the honest @Nullable override is exempted from the check.
    @SuppressWarnings("NullAway")
    @Override
    public @Nullable ProgramElement getChildAt(int index) {
        return null;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnCcatchContinueWildcardParameterDeclaration(this);
    }

}
