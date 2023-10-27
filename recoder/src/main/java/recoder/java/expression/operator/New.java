/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.*;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.TypeDeclarationContainer;
import recoder.java.expression.ExpressionStatement;
import recoder.java.reference.ConstructorReference;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.ReferenceSuffix;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTList;

/**
 * The object allocation operator. There are two variants for New:
 * <OL>
 * <LI>Class constructor call <BR>
 * <tt>new XYZ(a<sub>1</sub>, ..., a<sub>n</sub>)</tt><BR>
 * if getType() instanceof UserType
 * <LI>Anonymous Inner Class definition and construction <BR>
 * <tt>new XYZ(a<sub>1</sub>, ..., a<sub>n</sub>)
 * { m<sub>1</sub>, ..., m<sub>k</sub> }</tt> <BR>
 * if getType() instanceof UserType && getClassDeclaration() !=<tt>null</tt>
 * </OL>
 * The access path is <tt>null</tt> in most cases, except when an inner class constructor is invoked
 * from an outer instance.
 */

public class New extends TypeOperator implements ConstructorReference, ExpressionStatement,
        ReferencePrefix, ReferenceSuffix, TypeDeclarationContainer {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -4983184360698832328L;

    /**
     * Anonymous class.
     */
    protected ClassDeclaration anonymousClass;

    /**
     * Access path.
     */
    protected ReferencePrefix accessPath;

    /**
     * Reference parent.
     */

    protected ReferenceSuffix referenceParent;

    /**
     * Statement parent.
     */
    protected StatementContainer statementParent;

    /**
     * New.
     */

    public New() {
        // nothing to do
    }

    /**
     * New.
     *
     * @param accessPath a reference prefix.
     * @param constructorName a type reference.
     * @param arguments an expression mutable list.
     */

    public New(ReferencePrefix accessPath, TypeReference constructorName,
            ASTList<Expression> arguments) {
        setReferencePrefix(accessPath);
        setTypeReference(constructorName);
        setArguments(arguments);
        makeParentRoleValid();
    }

    /**
     * New.
     *
     * @param accessPath a reference prefix.
     * @param constructorName a type reference.
     * @param arguments an expression mutable list.
     * @param anonymousClass a class declaration.
     */

    public New(ReferencePrefix accessPath, TypeReference constructorName,
            ASTList<Expression> arguments, ClassDeclaration anonymousClass) {
        this(accessPath, constructorName, arguments);
        setClassDeclaration(anonymousClass);
        makeParentRoleValid();
    }

    /**
     * New.
     *
     * @param proto a new.
     */

    protected New(New proto) {
        super(proto);
        if (proto.anonymousClass != null) {
            anonymousClass = proto.anonymousClass.deepClone();
        }
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

    public New deepClone() {
        return new New(this);
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (children != null) {
            for (int i = children.size() - 1; i >= 0; i -= 1) {
                children.get(i).setExpressionContainer(this);
            }
        }
        if (accessPath != null) {
            accessPath.setReferenceSuffix(this);
        }
        if (anonymousClass != null) {
            anonymousClass.setParent(this);
        }
    }

    public SourceElement getFirstElement() {
        return (accessPath != null) ? accessPath.getFirstElement() : this;
    }

    public SourceElement getLastElement() {
        return getChildAt(getChildCount() - 1).getLastElement();
    }

    /**
     * Get AST parent.
     *
     * @return the non terminal program element.
     */

    public NonTerminalProgramElement getASTParent() {
        if (statementParent != null) {
            return statementParent;
        } else if (expressionParent != null) {
            return expressionParent;
        } else {
            return referenceParent;
        }
    }

    /**
     * Get arity.
     *
     * @return the int value.
     */

    public int getArity() {
        return 0;
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 0;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public int getNotation() {
        return PREFIX;
    }

    /**
     * Get statement container.
     *
     * @return the statement container.
     */
    public StatementContainer getStatementContainer() {
        return statementParent;
    }

    /**
     * Set statement container.
     *
     * @param parent a statement container.
     */

    public void setStatementContainer(StatementContainer parent) {
        statementParent = parent;
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
     * @param parent an expression container.
     */

    public void setExpressionContainer(ExpressionContainer parent) {
        expressionParent = parent;
    }

    /**
     * Get class declaration.
     *
     * @return the class declaration.
     */

    public ClassDeclaration getClassDeclaration() {
        return anonymousClass;
    }

    /**
     * Set class declaration.
     *
     * @param decl a class declaration.
     */

    public void setClassDeclaration(ClassDeclaration decl) {
        anonymousClass = decl;
    }

    /**
     * Get the number of type declarations in this container.
     *
     * @return the number of type declarations.
     */

    public int getTypeDeclarationCount() {
        return (anonymousClass != null) ? 1 : 0;
    }

    /*
     * Return the type declaration at the specified index in this node's "virtual" type declaration
     * array. @param index an index for a type declaration. @return the type declaration with the
     * given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public TypeDeclaration getTypeDeclarationAt(int index) {
        if (anonymousClass != null && index == 0) {
            return anonymousClass;
        }
        throw new ArrayIndexOutOfBoundsException();
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

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */

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
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0 (IDX): parameter
        // role 1: type reference (for type operators only)
        // role 2: prefix (for New only)
        // role 3: class declaration (for New only)
        // role 4 (IDX): type arguments
        if (children != null) {
            int index = children.indexOf(child);
            if (index >= 0) {
                return (index << 4) | 0;
            }
        }
        if (typeReference == child) {
            return 1;
        }
        if (accessPath == child) {
            return 2;
        }
        if (anonymousClass == child) {
            return 3;
        }
        return -1;
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
        count = (children == null) ? 0 : children.size();
        for (int i = 0; i < count; i++) {
            if (children.get(i) == p) {
                if (q == null) {
                    children.remove(i);
                } else {
                    Expression r = (Expression) q;
                    children.set(i, r);
                    r.setExpressionContainer(this);
                }
                return true;
            }
        }
        if (typeReference == p) {
            TypeReference r = (TypeReference) q;
            typeReference = r;
            if (r != null) {
                r.setParent(this);
            }
            return true;
        }
        if (accessPath == p) {
            ReferencePrefix r = (ReferencePrefix) q;
            accessPath = r;
            if (r != null) {
                r.setReferenceSuffix(this);
            }
            return true;
        }
        if (anonymousClass == p) {
            ClassDeclaration r = (ClassDeclaration) q;
            anonymousClass = r;
            if (r != null) {
                r.setParent(this);
            }
            return true;
        }
        return false;
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
     * @param x a reference prefix.
     */

    public void setReferencePrefix(ReferencePrefix x) {
        accessPath = x;
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
     * @param path a reference suffix.
     */

    public void setReferenceSuffix(ReferenceSuffix path) {
        referenceParent = path;
    }

    /**
     * Get arguments.
     *
     * @return the expression mutable list.
     */

    public ASTList<Expression> getArguments() {
        return children;
    }

    /**
     * Set arguments.
     *
     * @param list an expression mutable list.
     */

    public void setArguments(ASTList<Expression> list) {
        children = list;
    }

    public void accept(SourceVisitor v) {
        v.visitNew(this);
    }

}
