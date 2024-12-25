/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.Label;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.visitor.Visitor;

import java.util.List;


/**
 * Continue.
 *
 */
public class Continue extends LabelJumpStatement {

    /**
     * Continue.
     */
    public Continue() {
        super();
    }

    /**
     * Continue.
     *
     * @param label
     *        an identifier.
     */
    public Continue(Label label) {
        super(label);
    }


    public Continue(PositionInfo pi, List<Comment> c, Label name) {
        super(pi, c, name);
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnContinue(this);
    }
}
