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
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NullMarked;

/**
 * A record pattern (JLS 14.30.1), e.g. {@code Point(int x, int y)} in
 * {@code p instanceof Point(int x, int y)}.
 *
 * <p>
 * The component patterns are matched, in declaration order, against the record components; the
 * components are read through the record's accessor methods. A record pattern never matches
 * {@code null}.
 *
 * @author Alexander Weigl
 */
@NullMarked
public class RecordPattern extends Pattern {

    private final TypeReference typeReference;
    private final ImmutableArray<RecordPatternComponent> components;

    public RecordPattern(TypeReference typeReference,
            ImmutableArray<RecordPatternComponent> components) {
        this(PositionInfo.UNDEFINED, List.of(), typeReference, components);
    }

    public RecordPattern(ExtList children) {
        super(children);
        this.typeReference = Objects.requireNonNull(children.get(TypeReference.class));
        this.components = new ImmutableArray<>(children.collect(RecordPatternComponent.class));
    }

    public RecordPattern(PositionInfo pi, List<Comment> comments, TypeReference typeReference,
            ImmutableArray<RecordPatternComponent> components) {
        super(pi, comments);
        this.typeReference = Objects.requireNonNull(typeReference);
        this.components = Objects.requireNonNull(components);
    }

    /**
     * @return the record type of this pattern
     */
    public TypeReference getTypeReference() {
        return typeReference;
    }

    /**
     * @return the component patterns in record component declaration order
     */
    public ImmutableArray<RecordPatternComponent> getComponents() {
        return components;
    }

    @Override
    public int getChildCount() {
        return 1 + components.size();
    }

    @Override
    public ProgramElement getChildAt(int index) {
        if (index == 0) {
            return typeReference;
        }
        if (index > 0 && index <= components.size()) {
            return components.get(index - 1);
        }
        throw new IndexOutOfBoundsException("RecordPattern has no child " + index);
    }

    @Override
    public SourceElement getLastElement() {
        return components.isEmpty() ? typeReference : components.get(components.size() - 1);
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnRecordPattern(this);
    }
}
