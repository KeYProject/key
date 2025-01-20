/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration;

import recoder.abstraction.AnnotationUse;
import recoder.java.*;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceContainer;
import recoder.list.generic.ASTList;

/**
 * Use of an annotation, usually within a declaration. However, it may occur as part as an
 * ElementValuePair, so the interface Expression is implemented as well.
 *
 * @author gutzmann
 */
public class AnnotationUseSpecification extends JavaNonTerminalProgramElement
        implements AnnotationUse, DeclarationSpecifier, TypeReferenceContainer, Expression {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 6354411799881814722L;

    /**
     * Parent. Either an expression container, a declaration, or a PackageSpecification
     */
    protected NonTerminalProgramElement parent;

    protected TypeReference reference;

    protected ASTList<AnnotationElementValuePair> elementValuePairs;

    /**
     *
     */
    public AnnotationUseSpecification() {
        super();
    }

    public AnnotationUseSpecification(TypeReference reference) {
        this.reference = reference;
        makeParentRoleValid();
    }

    /**
     * @param proto
     */
    public AnnotationUseSpecification(AnnotationUseSpecification proto) {
        super(proto);
        this.reference = (TypeReference) proto.parent.deepClone();
        this.elementValuePairs = proto.elementValuePairs.deepClone();
        makeParentRoleValid();
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.SourceElement#accept(recoder.java.SourceVisitor)
     */
    public void accept(SourceVisitor v) {
        v.visitAnnotationUse(this);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.SourceElement#deepClone()
     */
    public AnnotationUseSpecification deepClone() {
        return new AnnotationUseSpecification(this);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.NonTerminalProgramElement#getChildCount()
     */
    public int getChildCount() {
        int res = 0;
        if (reference != null) {
            res++;
        }
        if (elementValuePairs != null) {
            res += elementValuePairs.size();
        }
        return res;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.NonTerminalProgramElement#getChildAt(int)
     */
    public ProgramElement getChildAt(int index) {
        if (reference != null) {
            if (index == 0) {
                return reference;
            }
            index--; // correct offset
        }
        return elementValuePairs.get(index);// may throw IndexOutOfBoundsException
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.NonTerminalProgramElement#getChildPositionCode(recoder.java.ProgramElement)
     */
    public int getChildPositionCode(ProgramElement child) {
        if (child == null) {
            throw new NullPointerException();
        }
        // role 0: reference
        // role 1 (idx): element value pair
        if (child == reference) {
            return 0;
        }
        if (elementValuePairs != null) {
            int idx = elementValuePairs.indexOf(child);
            if (idx >= -1) {
                return (idx << 4) | 1;
            }
        }
        return -1;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.NonTerminalProgramElement#makeParentRoleValid()
     */
    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (reference != null) {
            reference.setParent(this);
        }
        if (elementValuePairs != null) {
            for (AnnotationElementValuePair elementValuePair : elementValuePairs) {
                elementValuePair.setParent(this);
            }
        }
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.NonTerminalProgramElement#replaceChild(recoder.java.ProgramElement,
     * recoder.java.ProgramElement)
     */
    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null) {
            throw new NullPointerException();
        }
        if (p == reference) {
            TypeReference tr = (TypeReference) q;
            reference = tr;
            if (tr != null) {
                tr.setParent(this);
            }
            return true;
        }
        for (int i = 0; i < elementValuePairs.size(); i++) {
            AnnotationElementValuePair evp = elementValuePairs.get(i);
            if (p == evp) {
                if (q == null) {
                    elementValuePairs.remove(i);
                } else {
                    AnnotationElementValuePair r = (AnnotationElementValuePair) q;
                    elementValuePairs.set(i, r);
                    r.setParent(this);
                }
            }
        }
        return false;
    }

    /**
     * Get AST parent.
     *
     * @return the non terminal program element.
     */

    public NonTerminalProgramElement getASTParent() {
        return parent;
    }

    /**
     * Get parent iff it is a declaration.
     *
     * @return the declaration.
     */

    public Declaration getParentDeclaration() {
        return parent instanceof Declaration ? (Declaration) parent : null;
    }

    /**
     * Set parent.
     *
     * @param parent a declaration.
     */

    public void setParent(Declaration parent) {
        this.parent = parent;
    }

    public void setParent(PackageSpecification parent) {
        this.parent = parent;
    }

    public TypeReference getTypeReference() {
        return reference;
    }

    public void setTypeReference(TypeReference tr) {
        this.reference = tr;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.reference.TypeReferenceContainer#getTypeReferenceCount()
     */
    public int getTypeReferenceCount() {
        return reference == null ? 0 : 1;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.reference.TypeReferenceContainer#getTypeReferenceAt(int)
     */
    public TypeReference getTypeReferenceAt(int index) {
        if (index == 0 && reference != null) {
            return reference;
        }
        throw new ArrayIndexOutOfBoundsException(index);
    }

    public ASTList<AnnotationElementValuePair> getElementValuePairs() {
        return elementValuePairs;
    }

    public void setElementValuePairs(ASTList<AnnotationElementValuePair> elementValuePairs) {
        this.elementValuePairs = elementValuePairs;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.Expression#getExpressionContainer()
     */
    public ExpressionContainer getExpressionContainer() {
        return parent instanceof ExpressionContainer ? (ExpressionContainer) parent : null;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.Expression#setExpressionContainer(recoder.java.ExpressionContainer)
     */
    public void setExpressionContainer(ExpressionContainer c) {
        parent = c;
    }

}
