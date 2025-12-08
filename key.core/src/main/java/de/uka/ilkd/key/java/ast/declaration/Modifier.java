/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.declaration;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.JavaProgramElement;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.logic.SyntaxElement;

/**
 * Modifier. taken from COMPOST and changed to achieve an immutable structure
 */

public abstract class Modifier extends JavaProgramElement {

    /**
     * Modifier.
     */

    public Modifier() {}

    /**
     * Modifier.
     */
    public Modifier(PositionInfo pi, List<Comment> c) {
        super(pi, c);
    }

    /**
     * Get symbol.
     *
     * @return the string.
     */

    protected abstract String getSymbol();

    /**
     * Get symbol text.
     *
     * @return the symbol text.
     */
    public String getText() {
        return getSymbol();
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnModifier(this);
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException(getClass() + " " + this + " has no children");
    }
}
