/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import java.util.List;

import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * While.
 */

public class While extends LoopStatement {
    /**
     * While.
     *
     * @param guard
     *        an expression.
     * @param body
     *        a statement.
     * @param pos
     *        a PositionInformation.
     */

    public While(Expression guard, Statement body, PositionInfo pos, ExtList comments) {
        super(guard, body, comments, pos);
    }

    /**
     * create a new While statement with no position info and no comments but guard and body set
     *
     * @param guard
     *        an expression.
     * @param body
     *        a statement.
     */

    public While(Expression guard, Statement body) {
        super(guard, body, new ExtList());
    }

    /**
     * While.
     *
     * @param guard
     *        an expression.
     * @param body
     *        a statement.
     * @param pos
     *        a PositionInformation.
     */

    public While(Expression guard, Statement body, PositionInfo pos) {
        super(guard, body, pos);
    }

    public While(PositionInfo pi, List<Comment> c, Guard guard, Statement body) {
        super(pi, c, null, null, guard, body, ImmutableSLList.nil());
    }

    public While(PositionInfo pi, List<Comment> c, Guard guard, Statement body,
            List<TextualJMLConstruct> specs) {
        super(pi, c, null, null, guard, body, ImmutableList.fromList(specs));
    }

    public SourceElement getLastElement() {
        return (body != null) ? body.getLastElement() : this;
    }

    /**
     * Is checked before iteration.
     *
     * @return the boolean value.
     */

    public boolean isCheckedBeforeIteration() {
        return true;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnWhile(this);
    }
}
