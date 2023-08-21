/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.reference;

import recoder.java.*;
import recoder.list.generic.ASTList;

/**
 * Array reference.
 *
 * @author <TT>AutoDoc</TT>
 */

public class ArrayReference extends JavaNonTerminalProgramElement implements Reference, Expression,
        ReferencePrefix, ReferenceSuffix, ExpressionContainer, TypeReferenceContainer {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 5264208667205795216L;

    /**
     * Access parent when used as a reference prefix (e.g. <CODE>a[5].clone()
     * </CODE>).
     */
    protected ReferenceSuffix accessParent;

    /**
     * Parent.
     */
    protected ExpressionContainer parent;

    /**
     * Access path.
     */
    protected ReferencePrefix accessPath;

    /**
     * Inits.
     */
    protected ASTList<Expression> inits;

    /**
     * Array reference.
     */
    public ArrayReference() {
        // nothing to do
    }

    /**
     * Array reference.
     *
     * @param accessPath a reference prefix.
     * @param initializers an expression mutable list.
     */

    public ArrayReference(ReferencePrefix accessPath, ASTList<Expression> initializers) {
        setReferencePrefix(accessPath);
        setDimensionExpressions(initializers);
        makeParentRoleValid();
    }

    /**
     * Array reference.
     *
     * @param proto an array reference.
     */

    protected ArrayReference(ArrayReference proto) {
        super(proto);
        if (proto.accessPath != null) {
            accessPath = (ReferencePrefix) proto.accessPath.deepClone();
        }
        if (proto.inits != null) {
            inits = proto.inits.deepClone();
        }
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public ArrayReference deepClone() {
        return new ArrayReference(this);
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (accessPath != null) {
            accessPath.setReferenceSuffix(this);
        }
        if (inits != null) {
            for (int i = inits.size() - 1; i >= 0; i -= 1) {
                inits.get(i).setExpressionContainer(this);
            }
        }
    }

    /**
     * Get AST parent.
     *
     * @return the non terminal program element.
     */

    public NonTerminalProgramElement getASTParent() {
        if (parent != null) {
            return parent;
        } else {
            return accessParent;
        }
    }

    /**
     * Get the number of expressions in this container.
     *
     * @return the number of expressions.
     */

    public int getExpressionCount() {
        int c = 0;
        if (accessPath instanceof Expression) {
            c += 1;
        }
        if (inits != null) {
            c += inits.size();
        }
        return c;
    }

    /*
     * Return the expression at the specified index in this node's "virtual" expression
     * array. @param index an index for an expression. @return the expression with the given
     * index. @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public Expression getExpressionAt(int index) {
        if (accessPath instanceof Expression) {
            if (index == 0) {
                return (Expression) accessPath;
            }
            index--;
        }
        if (inits != null) {
            return inits.get(index);
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
        int count;
        if (accessPath == p) {
            ReferencePrefix r = (ReferencePrefix) q;
            accessPath = r;
            if (r != null) {
                r.setReferenceSuffix(this);
            }
            return true;
        }
        count = (inits == null) ? 0 : inits.size();
        for (int i = 0; i < count; i++) {
            if (inits.get(i) == p) {
                if (q == null) {
                    inits.remove(i);
                } else {
                    Expression r = (Expression) q;
                    inits.set(i, r);
                    r.setExpressionContainer(this);
                }
                return true;
            }
        }
        return false;
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
        if (accessPath instanceof TypeReference && index == 0) {
            return (TypeReference) accessPath;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get reference suffix.
     *
     * @return the reference suffix.
     */

    public ReferenceSuffix getReferenceSuffix() {
        return accessParent;
    }

    /**
     * Set reference suffix.
     *
     * @param path a reference suffix.
     */

    public void setReferenceSuffix(ReferenceSuffix path) {
        this.accessParent = path;
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
     * Set reference prefix.
     *
     * @param accessPath a reference prefix.
     */

    public void setReferencePrefix(ReferencePrefix accessPath) {
        this.accessPath = accessPath;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        int result = 0;
        if (accessPath != null) {
            result++;
        }
        if (inits != null) {
            result += inits.size();
        }
        return result;
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
            index--;
        }
        if (inits != null) {
            return inits.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0: prefix
        // role 1 (IDX): parameters
        if (accessPath == child) {
            return 0;
        }
        if (inits != null) {
            int index = inits.indexOf(child);
            if (index >= 0) {
                return (index << 4) | 1;
            }
        }
        return -1;
    }

    /**
     * Get expression container.
     *
     * @return the expression container.
     */

    public ExpressionContainer getExpressionContainer() {
        return parent;
    }

    /**
     * Set expression container.
     *
     * @param c an expression container.
     */

    public void setExpressionContainer(ExpressionContainer c) {
        parent = c;
    }

    /**
     * Get dimension expressions.
     *
     * @return the expression mutable list.
     */

    public ASTList<Expression> getDimensionExpressions() {
        return inits;
    }

    /**
     * Set dimension expressions.
     *
     * @param list an expression mutable list.
     */

    public void setDimensionExpressions(ASTList<Expression> list) {
        inits = list;
    }

    public SourceElement getFirstElement() {
        return (accessPath == null) ? this : accessPath.getFirstElement();
    }

    public void accept(SourceVisitor v) {
        v.visitArrayReference(this);
    }
}
