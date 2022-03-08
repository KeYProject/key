// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;

import javax.annotation.Nonnull;
import java.util.List;

public class While extends LoopStatement {
    public While(PositionInfo pi, List<Comment> comments, IGuard guard, Statement body) {
        super(pi, comments, null, null, guard, body);
    }

    /**
     * While.
     *
     * @param guard an expression.
     * @param body  a statement.
     * @param pos   a PositionInformation.
     */
    public While(Expression guard, Statement body, PositionInfo pos, ExtList comments) {
        super(guard, body, comments, pos);
    }

    /**
     * create a new While statement with no position info and no comments but guard and body set
     *
     * @param guard an expression.
     * @param body  a statement.
     */
    public While(Expression guard, Statement body) {
        super(guard, body, new ExtList());
    }

    /**
     * While.
     *
     * @param guard an expression.
     * @param body  a statement.
     * @param pos   a PositionInformation.
     */

    public While(Expression guard, Statement body, PositionInfo pos) {
        super(guard, body, pos);
    }

    @Override
    @Nonnull
    public SourceElement getLastElement() {
        return (body != null) ? body.getLastElement() : this;
    }

    /**
     * Is checked before iteration.
     *
     * @return the boolean value.
     */

    @Override
    public boolean isCheckedBeforeIteration() {
        return true;
    }

    /**
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     *
     * @param v the Visitor
     */
    @Override
    public void visit(Visitor v) {
        v.performActionOnWhile(this);
    }

    @Override
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printWhile(this);
    }
}
