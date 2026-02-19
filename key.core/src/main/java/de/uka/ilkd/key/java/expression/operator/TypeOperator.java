/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.AnnotationUseSpecification;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.reference.TypeReferenceContainer;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 * Type operator.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class TypeOperator extends Operator implements TypeReferenceContainer {

    /**
     * Type reference.
     */
    protected final TypeReference typeReference;

    /**
     * Annotations.
     */
    protected final ImmutableArray<AnnotationUseSpecification> annotations;


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes. May contain: a TypeReference
     *        (the referred type) 2 of Expression (the first Expression as left hand side, the
     *        second as right hand side), Comments
     */
    protected TypeOperator(ExtList children) {
        super(children);
        typeReference = children.get(TypeReference.class);
        annotations = new ImmutableArray<>(
            children.collect(AnnotationUseSpecification.class));
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes. May contain: a TypeReference
     *        (the referred type) 2 of Expression (the first Expression as left hand side, the
     *        second as right hand side), Comments
     */
    protected TypeOperator(ExtList children, PositionInfo pi) {
        super(children);
        typeReference = children.get(TypeReference.class);
        annotations = new ImmutableArray<>(
            children.collect(AnnotationUseSpecification.class));
    }

    protected TypeOperator(Expression unaryChild, TypeReference typeref) {
        super(unaryChild);
        typeReference = typeref;
        annotations = null;
    }

    protected TypeOperator(Expression[] arguments, TypeReference typeref) {
        super(arguments);
        typeReference = typeref;
        annotations = null;
    }

    protected TypeOperator(Expression[] arguments, TypeReference typeref,
            ImmutableArray<AnnotationUseSpecification> annotations) {
        super(arguments);
        typeReference = typeref;
        this.annotations = annotations;
    }

    protected TypeOperator() {
        typeReference = null;
        annotations = null;
    }

    /**
     * Get the number of type references in this container.
     *
     * @return the number of type references.
     */
    public int getTypeReferenceCount() {
        return (typeReference != null) ? 1 : 0;
    }

    /*
     * Return the type reference at the specified index in this node's "virtual" type reference
     * array.
     *
     * @param index an index for a type reference.
     *
     * @return the type reference with the given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
     */

    public TypeReference getTypeReferenceAt(int index) {
        if (typeReference != null && index == 0) {
            return typeReference;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get type reference.
     *
     * @return the type reference.
     */
    public TypeReference getTypeReference() {
        return typeReference;
    }

    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        return getKeYJavaType(javaServ);
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
        return getTypeReference().getKeYJavaType();
    }

    /**
     * Get the annotations.
     *
     * @return the annotations.
     */
    public ImmutableArray<AnnotationUseSpecification> getAnnotations() {
        return annotations;
    }
}
