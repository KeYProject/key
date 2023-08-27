/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclarationContainer;
import de.uka.ilkd.key.java.expression.ExpressionStatement;
import de.uka.ilkd.key.java.reference.ConstructorReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.ReferenceSuffix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * The object allocation operator. There are two variants for New:
 * <OL>
 * <LI>Class constructor call <BR>
 * <tt>new XYZ(a<sub>1</sub>, ..., a<sub>n</sub>)</tt> <BR>
 * if getType() instanceof UserType
 * <LI>Anonymous Inner Class definition and construction <BR>
 * <tt>new XYZ(a<sub>1</sub>, ..., a<sub>n</sub>)
 *  { m<sub>1</sub>, ..., m<sub>k</sub> }</tt> <BR>
 * if getType() instanceof UserType {@literal &&} getClassDeclaration() {@literal !=} <tt>null</tt>
 * </OL>
 * The access path is <tt>null</tt> in most cases, except when an inner class constructor is invoked
 * from an outer instance.
 */

public class New extends TypeOperator implements ConstructorReference, ExpressionStatement,
        ReferencePrefix, ReferenceSuffix, TypeDeclarationContainer {


    protected final ClassDeclaration anonymousClass;
    protected final ReferencePrefix accessPath;


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes. a ClassDeclaration (in case
     *        of an anonymous class decl) a TypeReference (the referred type) 2 of Expression (the
     *        first Expression as left hand side, the second as right hand side), Comments; does NOT
     *        contain: a ReferencePrefix for the constructor as it might be mixed up with the
     *        TypeReference
     * @param rp a ReferencePrefix as access path for the constructor
     */
    public New(ExtList children, ReferencePrefix rp) {
        super(children);
        anonymousClass = children.get(ClassDeclaration.class);
        accessPath = rp;
    }


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes. a ClassDeclaration (in case
     *        of an anonymous class decl) a TypeReference (the referred type) 2 of Expression (the
     *        first Expression as left hand side, the second as right hand side), Comments; does NOT
     *        contain: a ReferencePrefix for the constructor as it might be mixed up with the
     *        TypeReference
     * @param rp a ReferencePrefix as access path for the constructor
     */
    public New(ExtList children, ReferencePrefix rp, PositionInfo pi) {
        super(children, pi);
        anonymousClass = children.get(ClassDeclaration.class);
        accessPath = rp;
    }


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param type a TypeReference (the referred type)
     * @param rp a ReferencePrefix as access path for the constructor
     */
    public New(Expression[] arguments, TypeReference type, ReferencePrefix rp) {
        super(arguments, type);
        anonymousClass = null;
        accessPath = rp;
    }


    @Override
    public SourceElement getFirstElement() {
        return (accessPath != null) ? accessPath.getFirstElement() : this;
    }

    @Override
    public SourceElement getFirstElementIncludingBlocks() {
        return (accessPath != null) ? accessPath.getFirstElementIncludingBlocks() : this;
    }


    @Override
    public SourceElement getLastElement() {
        return getChildAt(getChildCount() - 1).getLastElement();
    }


    @Override
    public int getArity() {
        return 0;
    }


    @Override
    public int getPrecedence() {
        return 0;
    }


    @Override
    public int getNotation() {
        return PREFIX;
    }


    public ClassDeclaration getClassDeclaration() {
        return anonymousClass;
    }


    @Override
    public int getTypeDeclarationCount() {
        return (anonymousClass != null) ? 1 : 0;
    }


    @Override
    public TypeDeclaration getTypeDeclarationAt(int index) {
        if (anonymousClass != null && index == 0) {
            return anonymousClass;
        }
        throw new ArrayIndexOutOfBoundsException();
    }


    @Override
    public int getChildCount() {
        int result = 0;
        if (accessPath != null) {
            result++;
        }
        if (typeReference != null) {
            result++;
        }
        if (children != null) {
            result += children.size();
        }
        if (anonymousClass != null) {
            result++;
        }
        return result;
    }


    @Override
    public ProgramElement getChildAt(int index) {
        int len;
        if (accessPath != null) {
            if (index == 0) {
                return accessPath;
            }
            index--;
        }
        if (typeReference != null) {
            if (index == 0) {
                return typeReference;
            }
            index--;
        }
        if (children != null) {
            len = children.size();
            if (len > index) {
                return children.get(index);
            }
            index -= len;
        }
        if (anonymousClass != null) {
            if (index == 0) {
                return anonymousClass;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }


    /**
     * Get reference prefix.
     *
     * @return the reference prefix.
     */
    @Override
    public ReferencePrefix getReferencePrefix() {
        return accessPath;
    }


    @Override
    public void visit(Visitor v) {
        v.performActionOnNew(this);
    }


    public ReferencePrefix setReferencePrefix(ReferencePrefix r) {
        return this;
    }
}
