/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.statement;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.ast.declaration.VariableSpecification;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * For.
 *
 */

@NullMarked
public class For extends LoopStatement implements VariableScope {

    private static final ImmutableArray<VariableSpecification> EMPTY_VARSPECS =
        new ImmutableArray<>(new VariableSpecification[0]);

    /**
     * For. Used for the Recoder2KeY transformation
     *
     * @param inits
     *        a loop initializer mutable list.
     * @param guard
     *        an expression.
     * @param updates
     *        an expression mutable list.
     * @param body
     *        a statement.
     */
    public For(LoopInitializer[] inits, Expression guard, Expression[] updates, Statement body) {
        super(inits, guard, updates, body);
    }

    public For(@Nullable ILoopInit inits, IGuard guard, IForUpdates updates, Statement body) {
        super(inits, guard, updates, body);
    }

    public For(ExtList children) {
        super(children.get(ILoopInit.class), Objects.requireNonNull(children.get(IGuard.class),
            "For requires a guard"), children.get(IForUpdates.class),
            Objects.requireNonNull(children.get(Statement.class), "For requires a body"), children);
    }

    public For(PositionInfo pi, List<Comment> comments, @Nullable ILoopInit inits,
            @Nullable IForUpdates updates, IGuard guard, Statement body) {
        super(pi, comments, inits, updates, guard, body, ImmutableList.nil());
    }

    public <T> For(PositionInfo pi, List<Comment> comments, @Nullable ILoopInit inits,
            @Nullable IForUpdates updates, IGuard guard, Statement body,
            List<TextualJMLConstruct> specs) {
        super(pi, comments, inits, updates, guard, body, ImmutableList.fromList(specs));
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
            final ImmutableArray<LoopInitializer> inits2 =
                Objects.requireNonNull(inits.getInits(), "for-loop inits are mandatory");
            LoopInitializer li = inits2.get(0);
            if (li instanceof LocalVariableDeclaration) {
                return ((LocalVariableDeclaration) li).getVariables();
            }
        }
        return EMPTY_VARSPECS;
    }

    public @Nullable VariableSpecification getVariableInScope(String name) {
        if (inits != null) {
            final ImmutableArray<LoopInitializer> inits2 =
                Objects.requireNonNull(inits.getInits(), "for-loop inits are mandatory");
            LoopInitializer li = inits2.get(0);
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
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnFor(this);
    }
}
