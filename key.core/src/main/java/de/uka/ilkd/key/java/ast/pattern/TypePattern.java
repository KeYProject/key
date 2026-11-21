/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.pattern;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.ast.declaration.VariableSpecification;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

import org.jspecify.annotations.NullMarked;

/**
 * A type pattern that performs a type test (JLS 14.30.1), e.g. {@code String s} in
 * {@code o instanceof String s} or {@code R(String s)}.
 *
 * <p>
 * A nested type pattern is only a {@code TypePattern} if it is <em>not</em> unconditional for the
 * component type, i.e. if the component value has to be tested against the pattern type. See
 * {@link AnyPattern} for the unconditional case.
 *
 * @author Alexander Weigl
 */
@NullMarked
public class TypePattern extends Pattern {

    private final TypeReference typeReference;
    private final VariableSpecification variable;

    public TypePattern(TypeReference typeReference, VariableSpecification variable) {
        this(PositionInfo.UNDEFINED, List.of(), typeReference, variable);
    }

    public TypePattern(ExtList children) {
        super(children);
        this.typeReference = Objects.requireNonNull(children.get(TypeReference.class));
        this.variable = Objects.requireNonNull(children.get(VariableSpecification.class));
    }

    public TypePattern(PositionInfo pi, List<Comment> comments, TypeReference typeReference,
            VariableSpecification variable) {
        super(pi, comments);
        this.typeReference = Objects.requireNonNull(typeReference);
        this.variable = Objects.requireNonNull(variable);
    }

    /**
     * @return the type the matched value is tested against
     */
    public TypeReference getTypeReference() {
        return typeReference;
    }

    /**
     * @return the pattern variable declared by this pattern
     */
    public VariableSpecification getVariable() {
        return variable;
    }

    @Override
    public int getChildCount() {
        return 2;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        return switch (index) {
            case 0 -> typeReference;
            case 1 -> variable;
            default -> throw new IndexOutOfBoundsException("TypePattern has no child " + index);
        };
    }

    @Override
    public SourceElement getLastElement() {
        return variable;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnTypePattern(this);
    }
}
