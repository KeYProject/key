/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.reference;

import recoder.java.*;

/**
 * Super reference.
 *
 * @author <TT>AutoDoc</TT>
 */

public class SuperReference extends JavaNonTerminalProgramElement implements Reference, Expression,
        ReferencePrefix, ReferenceSuffix, ExpressionContainer, TypeReferenceContainer {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 1572767136419541150L;

    /**
     * Expression parent.
     */

    protected ExpressionContainer expressionParent;

    /**
     * Reference parent.
     */

    protected ReferenceSuffix referenceParent;

    /**
     * Access path.
     */

    protected ReferencePrefix accessPath;

    /**
     * Super reference.
     */

    public SuperReference() {
        makeParentRoleValid();
    }

    /**
     * Super reference.
     *
     * @param accessPath a reference expression.
     */

    public SuperReference(ReferencePrefix accessPath) {
        setReferencePrefix(accessPath);
        makeParentRoleValid();
    }

    /**
     * Super reference.
     *
     * @param proto a super reference.
     */

    protected SuperReference(SuperReference proto) {
        super(proto);
        if (proto.accessPath != null) {
            accessPath = (ReferencePrefix) proto.accessPath.deepClone();
        }
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public SuperReference deepClone() {
        return new SuperReference(this);
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (accessPath != null) {
            accessPath.setReferenceSuffix(this);
        }
    }

    public SourceElement getFirstElement() {
        return (accessPath == null) ? this : accessPath.getFirstElement();
    }

    /**
     * Get reference prefix.
     *
     * @return the reference prefix.
     */

    public ReferencePrefix getReferencePrefix() {
        return accessPath;
    }

    /**
     * qualifier instanceof ReferenceExpression
     */

    public void setReferencePrefix(ReferencePrefix p) {
        accessPath = p;
    }

    /**
     * Get reference suffix.
     *
     * @return the reference suffix.
     */

    public ReferenceSuffix getReferenceSuffix() {
        return referenceParent;
    }

    /**
     * Set reference suffix.
     *
     * @param x a reference suffix.
     */

    public void setReferenceSuffix(ReferenceSuffix x) {
        referenceParent = x;
    }

    /**
     * Get expression container.
     *
     * @return the expression container.
     */

    public ExpressionContainer getExpressionContainer() {
        return expressionParent;
    }

    /**
     * Set expression container.
     *
     * @param c an expression container.
     */

    public void setExpressionContainer(ExpressionContainer c) {
        expressionParent = c;
    }

    /**
     * Get AST parent.
     *
     * @return the non terminal program element.
     */

    public NonTerminalProgramElement getASTParent() {
        if (expressionParent != null) {
            return expressionParent;
        } else {
            return referenceParent;
        }
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        return (accessPath != null) ? 1 : 0;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */

    public ProgramElement getChildAt(int index) {
        if (accessPath != null) {
            if (index == 0) {
                return accessPath;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0: prefix
        if (accessPath == child) {
            return 0;
        }
        return -1;
    }

    /**
     * Get the number of expressions in this container.
     *
     * @return the number of expressions.
     */

    public int getExpressionCount() {
        return (accessPath instanceof Expression) ? 1 : 0;
    }

    /*
     * Return the expression at the specified index in this node's "virtual" expression
     * array. @param index an index for an expression. @return the expression with the given
     * index. @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public Expression getExpressionAt(int index) {
        if (accessPath instanceof Expression && index == 0) {
            return (Expression) accessPath;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get the number of type references in this container.
     *
     * @return the number of type references.
     */

    public int getTypeReferenceCount() {
        return (accessPath instanceof TypeReference) ? 1 : 0;
    }

    /*
     * Return the type reference at the specified index in this node's "virtual" type reference
     * array. @param index an index for a type reference. @return the type reference with the given
     * index. @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public TypeReference getTypeReferenceAt(int index) {
        if ((accessPath instanceof TypeReference) && index == 0) {
            return (TypeReference) accessPath;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Replace a single child in the current node. The child to replace is matched by identity and
     * hence must be known exactly. The replacement element can be null - in that case, the child is
     * effectively removed. The parent role of the new child is validated, while the parent link of
     * the replaced child is left untouched.
     *
     * @param p the old child.
     * @param p the new child.
     * @return true if a replacement has occured, false otherwise.
     * @throws ClassCastException if the new child cannot take over the role of the old one.
     */

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null) {
            throw new NullPointerException();
        }
        if (accessPath == p) {
            ReferencePrefix r = (ReferencePrefix) q;
            accessPath = r;
            if (r != null) {
                r.setReferenceSuffix(this);
            }
            return true;
        }
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitSuperReference(this);
    }
}
