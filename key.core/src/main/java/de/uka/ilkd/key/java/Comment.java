/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.logic.SyntaxElement;

/**
 * Comment element of Java source code.
 */
public class Comment extends JavaSourceElement {

    private final String text;

    public Comment() {
        this.text = null;
    }

    public Comment(String text) {
        this.text = text;
    }

    public Comment(String text, PositionInfo pInfo) {
        super(pInfo);
        this.text = text;
    }

    public boolean isPrefixed() {
        return false;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnComment(this);
    }

    public String getText() {
        return text;
    }

    @Override
    public String toString() {
        return getText();
    }

    @Override
    public int hashCode() {
        int result = 17;
        result = 37 * result + getText().hashCode();
        return result;
    }

    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        if (!(o instanceof Comment cmp)) {
            return false;
        }
        return (getText().equals(cmp.getText()));
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("Comment has no children");
    }
}
