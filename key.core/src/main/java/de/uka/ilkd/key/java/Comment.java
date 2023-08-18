/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.visitor.Visitor;

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


    public String toString() {
        return getText();
    }


    /**
     * comments can be ignored
     */
    public boolean equalsModRenaming(SourceElement se, NameAbstractionTable nat) {
        return true;
    }

    public int hashCode() {
        int result = 17;
        result = 37 * result + getText().hashCode();
        return result;
    }

    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        if (!(o instanceof Comment)) {
            return false;
        }
        Comment cmp = (Comment) o;
        return (getText().equals(cmp.getText()));
    }
}
