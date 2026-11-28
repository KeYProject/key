/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.expression;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.StatementContainer;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.ast.statement.Branch;
import de.uka.ilkd.key.java.ast.statement.Yield;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

/**
 * A switch expression (JLS 15.28). The selector is evaluated once and its value decides which arm
 * provides the value of the whole expression; an arm provides it with a {@link Yield} statement.
 *
 * <p>
 * The type of the expression is the type of the first yielded value (Java requires all arms to be
 * compatible), falling back to the selector type if every arm completes abruptly.
 */
public class SwitchExpression extends JavaNonTerminalProgramElement implements Expression {

    private final Expression selector;
    private final ImmutableList<Branch> branches;

    /**
     * Creates a switch expression.
     *
     * @param pi the position information
     * @param comments the comments attached to this expression
     * @param selector the selector expression
     * @param branches the arms of the switch expression
     */
    public SwitchExpression(PositionInfo pi, List<Comment> comments, Expression selector,
            ImmutableList<Branch> branches) {
        super(pi, comments);
        this.selector = selector;
        this.branches = branches;
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes
     */
    public SwitchExpression(ExtList children) {
        super(children);
        this.selector = children.get(Expression.class);
        this.branches = ImmutableList.asArray(children.collect(Branch.class));
    }

    /**
     * @return the selector expression
     */
    public Expression getSelector() {
        return selector;
    }

    /**
     * @return the number of arms
     */
    public int getBranchCount() {
        return branches.size();
    }

    /**
     * @param index the arm index
     * @return the arm at the given index
     */
    public Branch getBranchAt(int index) {
        return branches.get(index);
    }

    @Override
    public int getChildCount() {
        return 1 + branches.size();
    }

    @Override
    public ProgramElement getChildAt(int index) {
        if (index == 0) {
            return selector;
        }
        return branches.get(index - 1);
    }

    @Override
    public KeYJavaType getKeYJavaType(Services services, ExecutionContext ec) {
        for (int i = 0; i < branches.size(); i++) {
            KeYJavaType type = findYieldType(branches.get(i), services, ec);
            if (type != null) {
                return type;
            }
        }
        return selector.getKeYJavaType(services, ec);
    }

    private static @Nullable KeYJavaType findYieldType(ProgramElement element, Services services,
            ExecutionContext ec) {
        if (element instanceof Yield yield && yield.getExpression() != null) {
            return yield.getExpression().getKeYJavaType(services, ec);
        }
        if (element instanceof StatementContainer container) {
            for (int i = 0; i < container.getStatementCount(); i++) {
                KeYJavaType type = findYieldType(container.getStatementAt(i), services, ec);
                if (type != null) {
                    return type;
                }
            }
        }
        return null;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnSwitchExpression(this);
    }
}
