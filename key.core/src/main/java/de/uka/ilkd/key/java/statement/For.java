/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 * For.
 *
 */

public class For extends LoopStatement implements VariableScope {

    private static final ImmutableArray<VariableSpecification> EMPTY_VARSPECS =
        new ImmutableArray<>(new VariableSpecification[0]);

    /**
     * For.
     */
    public For() {}

    /**
     * For. Used for the Recoder2KeY transformation
     *
     * @param inits a loop initializer mutable list.
     * @param guard an expression.
     * @param updates an expression mutable list.
     * @param body a statement.
     */
    public For(LoopInitializer[] inits, Expression guard, Expression[] updates, Statement body) {
        super(inits, guard, updates, body);
    }

    public For(ILoopInit inits, IGuard guard, IForUpdates updates, Statement body,
            ExtList comments) {
        super(inits, guard, updates, body, comments);
    }

    public For(ILoopInit inits, IGuard guard, IForUpdates updates, Statement body, ExtList comments,
            PositionInfo pos) {
        super(inits, guard, updates, body, comments, pos);
    }

    public For(ILoopInit inits, IGuard guard, IForUpdates updates, Statement body) {
        super(inits, guard, updates, body);
    }

    public For(ExtList children) {
        super(children.get(ILoopInit.class), children.get(IGuard.class),
            children.get(IForUpdates.class), children.get(Statement.class), children);
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

    public boolean isDefinedScope() {
        return true;
    }

    public ImmutableArray<VariableSpecification> getVariablesInScope() {
        if (inits != null) {
            LoopInitializer li = inits.getInits().get(0);
            if (li instanceof LocalVariableDeclaration) {
                return ((LocalVariableDeclaration) li).getVariables();
            }
        }
        return EMPTY_VARSPECS;
    }

    public VariableSpecification getVariableInScope(String name) {
        if (inits != null) {
            LoopInitializer li = inits.getInits().get(0);
            if (li instanceof LocalVariableDeclaration) {
                ImmutableArray<VariableSpecification> vars =
                    ((LocalVariableDeclaration) li).getVariables();
                for (int i = 0, s = vars.size(); i < s; i += 1) {
                    VariableSpecification v = vars.get(i);
                    if (name.equals(v.getName())) {
                        return v;
                    }
                }
            }
        }
        return null;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnFor(this);
    }
}
