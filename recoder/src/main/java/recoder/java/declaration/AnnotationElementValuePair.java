/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration;

import recoder.abstraction.ElementValuePair;
import recoder.java.*;
import recoder.java.expression.Literal;
import recoder.java.reference.AnnotationPropertyReference;

/**
 * @author gutzmann
 */
public class AnnotationElementValuePair extends JavaNonTerminalProgramElement
        implements ExpressionContainer, ElementValuePair {
    /**
     * serialization id
     */
    private static final long serialVersionUID = -8603363313540445285L;

    protected AnnotationUseSpecification parent;

    protected AnnotationPropertyReference element;

    protected Expression elementValue;

    /**
     *
     */
    public AnnotationElementValuePair() {
        super();
    }

    public AnnotationElementValuePair(AnnotationPropertyReference elem, Expression elementValue) {
        this.element = elem;
        this.elementValue = elementValue;
    }

    /**
     * @param proto
     */
    protected AnnotationElementValuePair(AnnotationElementValuePair proto) {
        super(proto);
        element = proto.element.deepClone();
        elementValue = proto.elementValue.deepClone();
        makeParentRoleValid();
    }

    /**
     * TODO move this somewhere where it belongs...
     *
     * @param expr
     * @return
     */
    static Object expressionToJavaObject(Expression expr) {
        if (expr instanceof Literal) {
            return ((Literal) expr).getEquivalentJavaType();
        }
        // TODO
        throw new RuntimeException("Do not understand type of expression "
            + "in AnnotationElementValuePair.getValue()... (TODO)");
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (element != null) {
            element.setParent(this);
        }
        if (elementValue != null) {
            elementValue.setExpressionContainer(this);
        }
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.NonTerminalProgramElement#getChildCount()
     */
    public int getChildCount() {
        int res = 0;
        if (element != null) {
            res++;
        }
        if (elementValue != null) {
            res++;
        }
        return res;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.NonTerminalProgramElement#getChildAt(int)
     */
    public ProgramElement getChildAt(int index) {
        int i = index;
        if (element != null) {
            if (i == 0) {
                return element;
            }
            i--;
        }
        if (elementValue != null) {
            if (i == 0) {
                return elementValue;
            }
            i--;
        }
        throw new ArrayIndexOutOfBoundsException(index);
    }

    public SourceElement getFirstElement() {
        return element != null ? element.getFirstElement()
                : (elementValue != null ? elementValue.getFirstElement() : this);
    }

    public SourceElement getLastElement() {
        return elementValue != null ? elementValue.getLastElement()
                : (element != null ? element.getLastElement() : this);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.NonTerminalProgramElement#getChildPositionCode(recoder.java.ProgramElement)
     */
    public int getChildPositionCode(ProgramElement child) {
        // role 0: element
        // role 1: elementValue
        if (child == element) {
            return 0;
        }
        if (child == elementValue) {
            return 1;
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
        if (p == element) {
            element = (AnnotationPropertyReference) q;
            if (element != null) {
                element.setParent(this);
            }
            return true;
        }
        if (p == elementValue) {
            elementValue = (Expression) q;
            if (elementValue != null) {
                elementValue.setExpressionContainer(this);
            }
            return true;
        }
        return false;
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
        v.visitElementValuePair(this);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.SourceElement#deepClone()
     */
    public AnnotationElementValuePair deepClone() {
        return new AnnotationElementValuePair(this);
    }

    public Expression getElementValue() {
        return elementValue;
    }

    public void setElementValue(Expression elementValue) {
        this.elementValue = elementValue;
    }

    public AnnotationPropertyReference getElement() {
        return element;
    }

    public void setElement(AnnotationPropertyReference ref) {
        this.element = ref;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.ExpressionContainer#getExpressionCount()
     */
    public int getExpressionCount() {
        return elementValue == null ? 0 : 1;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.ExpressionContainer#getExpressionAt(int)
     */
    public Expression getExpressionAt(int index) {
        if (index == 0 && elementValue != null) {
            return elementValue;
        }
        throw new ArrayIndexOutOfBoundsException(index);
    }

    public AnnotationUseSpecification getParent() {
        return parent;
    }

    public void setParent(AnnotationUseSpecification parent) {
        this.parent = parent;
    }

    public Object getValue() {
        return expressionToJavaObject(elementValue);
    }

    public String getElementName() {
        if (element == null) {
            return "(default value)"; // TODO correct text
        }
        return element.getIdentifier().getText();
    }

}
