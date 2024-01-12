/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression;

import recoder.java.*;
import recoder.list.generic.ASTList;

/**
 * @author Tobias Gutzmann
 */
public class ElementValueArrayInitializer extends JavaNonTerminalProgramElement
        implements Expression, ExpressionContainer {
    /**
     * serialization id
     */
    private static final long serialVersionUID = -3857746318263472090L;

    protected ExpressionContainer parent;
    protected ASTList<Expression> elementValues;

    /**
     *
     */
    public ElementValueArrayInitializer() {
        super();
    }

    /**
     * @param proto
     */
    protected ElementValueArrayInitializer(ElementValueArrayInitializer proto) {
        super(proto);
        if (proto.elementValues != null) {
            this.elementValues = proto.elementValues.deepClone();
        }
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.Expression#getExpressionContainer()
     */
    public ExpressionContainer getExpressionContainer() {
        return parent;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.Expression#setExpressionContainer(recoder.java.ExpressionContainer)
     */
    public void setExpressionContainer(ExpressionContainer c) {
        parent = c;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.Expression#deepClone()
     */
    public ElementValueArrayInitializer deepClone() {
        return new ElementValueArrayInitializer(this);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.ProgramElement#getASTParent()
     */
    public NonTerminalProgramElement getASTParent() {
        return parent;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.SourceElement#accept(recoder.java.SourceVisitor)
     */
    public void accept(SourceVisitor v) {
        v.visitElementValueArrayInitializer(this);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.ExpressionContainer#getExpressionCount()
     */
    public int getExpressionCount() {
        return elementValues == null ? 0 : elementValues.size();
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.ExpressionContainer#getExpressionAt(int)
     */
    public Expression getExpressionAt(int index) {
        if (elementValues != null) {
            return elementValues.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.NonTerminalProgramElement#getChildCount()
     */
    public int getChildCount() {
        return getExpressionCount();
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.NonTerminalProgramElement#getChildAt(int)
     */
    public ProgramElement getChildAt(int index) {
        return getExpressionAt(index);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.NonTerminalProgramElement#getChildPositionCode(recoder.java.ProgramElement)
     */
    public int getChildPositionCode(ProgramElement child) {
        // 0(IDX): elementValues
        if (elementValues == null) {
            return -1;
        }
        int idx = elementValues.indexOf(child);
        if (idx != -1) {
            return idx << 4;
        }
        return -1;
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
        int count;
        count = (elementValues == null) ? 0 : elementValues.size();
        for (int i = 0; i < count; i++) {
            if (elementValues.get(i) == p) {
                if (q == null) {
                    elementValues.remove(i);
                } else {
                    Expression r = (Expression) q;
                    elementValues.set(i, r);
                    r.setExpressionContainer(this);
                }
                return true;
            }
        }
        return false;
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (elementValues != null) {
            for (Expression e : elementValues) {
                e.setExpressionContainer(this);
            }
        }
    }

    public ASTList<Expression> getElementValues() {
        return elementValues;
    }

    public void setElementValues(ASTList<Expression> elementValues) {
        this.elementValues = elementValues;
    }

}
