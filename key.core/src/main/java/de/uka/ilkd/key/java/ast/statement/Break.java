/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.Label;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * Break.
 *
 */

public class Break extends LabelJumpStatement {

    /**
     * Break.
     */

    public Break() {
        super();
    }

    /**
     * Break.
     *
     * @param label
     *        a name for the label.
     */
    public Break(Label label) {
        super(label);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children
     *        the children of this AST element as KeY classes. May contain: Comments, a
     *        ProgramElementName (as label of the label jump statement)
     */
    public Break(ExtList children) {
        super(children);
        // label=(ProgramElementName)children.get(ProgramElementName.class);
    }

    public Break(PositionInfo pi, List<Comment> c, Label name) {
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
        v.performActionOnBreak(this);
    }
}
