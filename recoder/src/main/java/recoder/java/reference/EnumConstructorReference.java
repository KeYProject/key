/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.reference;

import recoder.java.*;
import recoder.java.declaration.*;
import recoder.list.generic.ASTList;

/**
 * @author Tobias Gutzmann
 */
public class EnumConstructorReference extends JavaNonTerminalProgramElement
        implements ConstructorReference, TypeDeclarationContainer {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 346152574064180781L;

    protected ClassDeclaration classDeclaration;

    protected ASTList<Expression> args;

    protected EnumConstantSpecification parent;

    public EnumConstructorReference() {
        super();
    }

    public EnumConstructorReference(ASTList<Expression> args, ClassDeclaration anonymousClass) {
        this.args = args;
        this.classDeclaration = anonymousClass;
        makeParentRoleValid();
    }

    protected EnumConstructorReference(EnumConstructorReference proto) {
        super(proto);
        if (proto.classDeclaration != null) {
            classDeclaration = proto.classDeclaration.deepClone();
        }
        if (proto.args != null) {
            args = proto.args.deepClone();
        }
    }

    public void accept(SourceVisitor v) {
        v.visitEnumConstructorReference(this);
    }

    public EnumConstructorReference deepClone() {
        return new EnumConstructorReference(this);
    }

    /**
     * Inherited through ConstructorReference. However, this kind of ConstructorReference cannot
     * appear as a statement. Always returns <code>null</code>
     *
     * @returns <code>null</code>
     */
    public StatementContainer getStatementContainer() {
        return null;
    }

    /**
     * @throws UnsupportedOperationException
     * @see getStatementContainer()
     */
    public void setStatementContainer(@SuppressWarnings("unused") StatementContainer c) {
        throw new UnsupportedOperationException();
    }

    public int getTypeDeclarationCount() {
        return classDeclaration == null ? 0 : 1;
    }

    public TypeDeclaration getTypeDeclarationAt(int index) {
        if (classDeclaration != null && index == 0) {
            return classDeclaration;
        }
        throw new ArrayIndexOutOfBoundsException(index);
    }

    public ProgramElement getChildAt(int index) {
        if (args != null) {
            int l = args.size();
            if (index < l) {
                return args.get(index);
            }
            index -= l;
        }
        if (classDeclaration != null) {
            if (index == 0) {
                return classDeclaration;
            }
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildCount() {
        return getTypeDeclarationCount() + (args == null ? 0 : args.size());
    }

    @Override
    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (classDeclaration != null) {
            classDeclaration.setParent(this);
        }
        if (args != null) {
            for (Expression e : args) {
                e.setExpressionContainer(this);
            }
        }
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null) {
            throw new NullPointerException();
        }
        if (p == classDeclaration) {
            classDeclaration = (ClassDeclaration) q;
            if (q != null) {
                classDeclaration.setParent(this);
            }
            return true;
        }
        int idx;
        if (args != null && (idx = args.indexOf(p)) != -1) {
            if (q == null) {
                args.remove(idx);
            } else {
                Expression s = (Expression) q;
                args.set(idx, s);
                s.setExpressionContainer(this);
            }
            return true;
        }
        return false;
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0 : classDeclaration
        // role 1(idx) : arg
        if (child == classDeclaration) {
            return 0;
        }
        if (args != null) {
            int idx = args.indexOf(child);
            if (idx != -1) {
                return (idx << 4) | 1;
            }
        }
        return -1;
    }

    /**
     * @return Returns the classDeclaration.
     */
    public final ClassDeclaration getClassDeclaration() {
        return classDeclaration;
    }

    /**
     * @param classDeclaration The classDeclaration to set.
     */
    public final void setClassDeclaration(ClassDeclaration classDeclaration) {
        this.classDeclaration = classDeclaration;
    }

    public ASTList<Expression> getArguments() {
        return args;
    }

    public void setArguments(ASTList<Expression> list) {
        this.args = list;
    }

    public NonTerminalProgramElement getASTParent() {
        return parent;
    }

    public void setParent(EnumConstantSpecification parent) {
        this.parent = parent;
    }

    public int getExpressionCount() {
        return args == null ? 0 : args.size();
    }

    public Expression getExpressionAt(int index) {
        if (args == null) {
            throw new ArrayIndexOutOfBoundsException(index);
        }
        return args.get(index);
    }

    public ASTList<TypeArgumentDeclaration> getTypeArguments() {
        return null;
    }

    public ProgramElement getFirstElement() {
        if (args != null && args.size() > 0) {
            return args.get(0);
        }
        return this;
    }

    public ProgramElement getLastElement() {
        if (classDeclaration != null) {
            return classDeclaration;
        }
        if (args != null && args.size() > 0) {
            return args.get(args.size() - 1);
        }
        return this;
    }

}
