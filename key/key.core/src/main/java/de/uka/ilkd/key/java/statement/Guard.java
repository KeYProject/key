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

/**
 * This class encapsulates a guard for a loop
 */
public final class Guard extends JavaNonTerminalProgramElement implements IGuard {
    @Nonnull
    private final Expression expr;

    public Guard(PositionInfo pi, List<Comment> comments, Expression expr) {
        super(pi, comments);
        this.expr = expr;
    }

    public Guard(Expression expression) {
        this(null, null, expression);
    }

    public Guard(ExtList children) {
        super(children);
        expr = children.get(Expression.class);
    }

    public Expression getExpression() {
        return expr;
    }

    public void visit(Visitor v) {
        v.performActionOnGuard(this);
    }

    public int getChildCount() {
        return 1;
    }

    public ProgramElement getChildAt(int index) {
        if (index == 0) return expr;
        return null;
    }

    public String toString() {
        return expr.toString();
    }
}