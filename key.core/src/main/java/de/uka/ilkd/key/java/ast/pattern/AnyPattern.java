/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.pattern;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.ast.declaration.VariableSpecification;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * A pattern that matches every value (JLS 14.30.1 "match-all pattern").
 *
 * <p>
 * This covers three source forms:
 * <ul>
 * <li>{@code var x}: no type reference, variable type inferred from the component,</li>
 * <li>an unconditional type pattern such as {@code Object o} for an {@code Object} component or
 * {@code Super s} for a {@code Sub} component: JLS 14.30.1 resolves it to an any pattern, so it
 * also matches {@code null},</li>
 * <li>{@code _}: no variable at all.</li>
 * </ul>
 *
 * <p>
 * Only a nested type pattern can be unconditional; top-level type patterns always perform a type
 * test and are represented by {@link TypePattern}.
 *
 * @author Alexander Weigl
 */
@NullMarked
public class AnyPattern extends Pattern {

    private final @Nullable TypeReference typeReference;
    private final @Nullable VariableSpecification variable;

    public AnyPattern(@Nullable TypeReference typeReference,
            @Nullable VariableSpecification variable) {
        this(PositionInfo.UNDEFINED, List.of(), typeReference, variable);
    }

    public AnyPattern(ExtList children) {
        super(children);
        this.typeReference = children.get(TypeReference.class);
        this.variable = children.get(VariableSpecification.class);
    }

    public AnyPattern(PositionInfo pi, List<Comment> comments,
            @Nullable TypeReference typeReference, @Nullable VariableSpecification variable) {
        super(pi, comments);
        this.typeReference = typeReference;
        this.variable = variable;
    }

    /**
     * @return the declared type of the pattern variable, or {@code null} for {@code var} and
     *         {@code _}
     */
    public @Nullable TypeReference getTypeReference() {
        return typeReference;
    }

    /**
     * @return the pattern variable, or {@code null} for {@code _}
     */
    public @Nullable VariableSpecification getVariable() {
        return variable;
    }

    @Override
    public int getChildCount() {
        return (typeReference != null ? 1 : 0) + (variable != null ? 1 : 0);
    }

    @Override
    public ProgramElement getChildAt(int index) {
        int i = index;
        if (typeReference != null) {
            if (i == 0) {
                return typeReference;
            }
            i--;
        }
        if (variable != null && i == 0) {
            return variable;
        }
        throw new IndexOutOfBoundsException("AnyPattern has no child " + index);
    }

    @Override
    public SourceElement getLastElement() {
        if (variable != null) {
            return variable;
        }
        return typeReference != null ? typeReference : this;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnAnyPattern(this);
    }
}
