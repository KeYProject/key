/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration;

import recoder.abstraction.AnnotationProperty;
import recoder.java.*;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTList;

/**
 * @author gutzmann
 */
public class AnnotationPropertyDeclaration extends MethodDeclaration
        implements AnnotationProperty, ExpressionContainer {
    /**
     * serialization id
     */
    private static final long serialVersionUID = -1319877992238107401L;

    protected Expression defaultValue;

    /**
     *
     */
    public AnnotationPropertyDeclaration() {
        super();
        makeParentRoleValid();
    }

    /**
     * @param modifiers
     * @param returnType
     * @param name
     * @param parameters
     * @param exceptions
     */
    public AnnotationPropertyDeclaration(ASTList<DeclarationSpecifier> modifiers,
            TypeReference returnType, Identifier name, Expression defaultValue) {
        super(modifiers, returnType, name, null, null);
        this.defaultValue = defaultValue;
        makeParentRoleValid();
    }

    /**
     * @param proto
     */
    protected AnnotationPropertyDeclaration(AnnotationPropertyDeclaration proto) {
        super(proto);
        if (proto.defaultValue != null) {
            defaultValue = proto.defaultValue.deepClone();
            defaultValue.setExpressionContainer(this);
        }
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.AnnotationProperty#getDefaultValue()
     */
    public Object getDefaultValue() {
        return AnnotationElementValuePair.expressionToJavaObject(defaultValue);
    }

    public void setDefaultValue(Expression e) {
        defaultValue = e;
    }

    public Expression getDefaultValueExpression() {
        return defaultValue;
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (defaultValue != null) {
            defaultValue.setExpressionContainer(this);
        }
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.ExpressionContainer#getExpressionCount()
     */
    public int getExpressionCount() {
        return defaultValue == null ? 0 : 1;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.ExpressionContainer#getExpressionAt(int)
     */
    public Expression getExpressionAt(int index) {
        if (index == 0 && defaultValue != null) {
            return defaultValue;
        }
        throw new ArrayIndexOutOfBoundsException(index);
    }

    public void accept(SourceVisitor v) {
        v.visitAnnotationPropertyDeclaration(this);
    }

    public AnnotationPropertyDeclaration deepClone() {
        return new AnnotationPropertyDeclaration(this);
    }

    public ProgramElement getChildAt(int index) {
        if (index == super.getChildCount() && defaultValue != null) {
            return defaultValue;
        }
        return super.getChildAt(index); // might throw ArrayIndexOutOfBoundsException
    }

    public int getChildCount() {
        return super.getChildCount() + (defaultValue == null ? 0 : 1);
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0-7: see MethodDeclaration
        // role 8: default value
        if (child == defaultValue) {
            return 8;
        }
        return super.getChildPositionCode(child);
    }

    public boolean isPrivate() {
        return false;
    }

    public boolean isProtected() {
        return false;
    }

    public boolean isPublic() {
        return true;
    }

    public boolean isVarArgMethod() {
        return false;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null) {
            throw new NullPointerException();
        }
        if (p == defaultValue) {
            Expression r = (Expression) q;
            defaultValue = r;
            if (r != null) {
                r.setExpressionContainer(this);
            }
            return true;
        }
        return super.replaceChild(p, q);
    }
}
