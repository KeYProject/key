/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration;

import recoder.java.*;
import recoder.list.generic.ASTList;

/**
 * Outer or inner class declaration. There are several types of class declarations:
 * <ul>
 * <li>package-less outer classes
 * <ul>
 * <li>getClassContainer() == null
 * <li>getStatementContainer() == null
 * <li>getName() != null
 * </ul>
 * <li>ordinary outer classes
 * <ul>
 * <li>getClassContainer() instanceof Package
 * <li>getStatementContainer() == null
 * <li>getName() != null
 * </ul>
 * <li>member classes
 * <ul>
 * <li>getClassContainer() instanceof ClassDeclaration
 * <li>getStatementContainer() == null
 * <li>getName() != null
 * </ul>
 * <li>local class
 * <ul>
 * <li>getClassContainer() == null
 * <li>getStatementContainer() != null
 * <li>getName() != null
 * </ul>
 * <li>local anonymous class
 * <ul>
 * <li>getClassContainer() == null <!--
 * <li>getStatementContainer() instanceof expression.New--> <!-- Fix by T.Gutzmann -->
 * <li>getStatementContainer() == null
 * <li>getName() == null
 * </ul>
 * </ul>
 * Anonymous local classes have exactly one supertype and no subtypes. <BR>
 * Binary classes may have only binary members.
 */
public class ClassDeclaration extends TypeDeclaration implements Statement {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -1520369925548201696L;

    /**
     * Extending.
     */
    protected Extends extending;

    /**
     * Type Parameters (Java 5)
     */
    protected ASTList<TypeParameterDeclaration> typeParameters;

    /**
     * Implementing.
     */
    protected Implements implementing;

    /**
     * Class declaration.
     */
    public ClassDeclaration() {
        // nothing to do here
    }

    /**
     * Construct a non-anonymous class.
     */
    public ClassDeclaration(ASTList<DeclarationSpecifier> declSpecs, Identifier name,
            Extends extended, Implements implemented, ASTList<MemberDeclaration> members,
            ASTList<TypeParameterDeclaration> typeParameters) {
        super(declSpecs, name);
        setExtendedTypes(extended);
        setImplementedTypes(implemented);
        setMembers(members);
        setTypeParameters(typeParameters);
        makeParentRoleValid();
    }

    public ClassDeclaration(ASTList<DeclarationSpecifier> declSpecs, Identifier name,
            Extends extended, Implements implemented, ASTList<MemberDeclaration> members) {
        this(declSpecs, name, extended, implemented, members, null);
    }

    /**
     * Class declaration.
     *
     * @param members a member declaration mutable list.
     */
    public ClassDeclaration(ASTList<MemberDeclaration> members) {
        setMembers(members);
        makeParentRoleValid();
    }

    /**
     * Class declaration.
     *
     * @param proto a class declaration.
     */
    protected ClassDeclaration(ClassDeclaration proto) {
        super(proto);
        if (proto.extending != null) {
            extending = proto.extending.deepClone();
        }
        if (proto.implementing != null) {
            implementing = proto.implementing.deepClone();
        }
        if (proto.typeParameters != null) {
            typeParameters = proto.typeParameters.deepClone();
        }
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */
    public ClassDeclaration deepClone() {
        return new ClassDeclaration(this);
    }

    /**
     * Make parent role valid.
     */
    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (extending != null) {
            extending.setParent(this);
        }
        if (implementing != null) {
            implementing.setParent(this);
        }
        if (typeParameters != null) {
            for (TypeParameterDeclaration tp : typeParameters) {
                tp.setParent(this);
            }
        }
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (declarationSpecifiers != null) {
            result += declarationSpecifiers.size();
        }
        if (name != null) {
            result++;
        }
        if (extending != null) {
            result++;
        }
        if (implementing != null) {
            result++;
        }
        if (members != null) {
            result += members.size();
        }
        if (typeParameters != null) {
            result += typeParameters.size();
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
        if (declarationSpecifiers != null) {
            len = declarationSpecifiers.size();
            if (len > index) {
                return declarationSpecifiers.get(index);
            }
            index -= len;
        }
        if (name != null) {
            if (index == 0) {
                return name;
            }
            index--;
        }
        if (typeParameters != null) {
            len = typeParameters.size();
            if (len > index) {
                return typeParameters.get(index);
            }
            index -= len;
        }
        if (extending != null) {
            if (index == 0) {
                return extending;
            }
            index--;
        }
        if (implementing != null) {
            if (index == 0) {
                return implementing;
            }
            index--;
        }
        if (members != null) {
            if (index < members.size()) {
                return members.get(index);
            }
            index -= members.size();
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0 (IDX): declaration specifier
        // role 1: identifier
        // role 2: extends
        // role 3: implements (no occurance in interfaces)
        // role 4 (IDX): members
        // role 5 (IDX): type parameters
        if (declarationSpecifiers != null) {
            int index = declarationSpecifiers.indexOf(child);
            if (index >= 0) {
                return (index << 4) | 0;
            }
        }
        if (name == child) {
            return 1;
        }
        if (extending == child) {
            return 2;
        }
        if (implementing == child) {
            return 3;
        }
        if (members != null) {
            int index = members.indexOf(child);
            if (index >= 0) {
                return (index << 4) | 4;
            }
        }
        if (typeParameters != null) {
            int index = typeParameters.size();
            if (index >= 0) {
                return (index << 4) | 5;
            }
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
        count = (declarationSpecifiers == null) ? 0 : declarationSpecifiers.size();
        for (int i = 0; i < count; i++) {
            if (declarationSpecifiers.get(i) == p) {
                if (q == null) {
                    declarationSpecifiers.remove(i);
                } else {
                    DeclarationSpecifier r = (DeclarationSpecifier) q;
                    declarationSpecifiers.set(i, r);
                    r.setParent(this);
                }
                return true;
            }
        }
        if (name == p) {
            Identifier r = (Identifier) q;
            name = r;
            if (r != null) {
                r.setParent(this);
            }
            return true;
        }
        if (extending == p) {
            Extends r = (Extends) q;
            extending = r;
            if (r != null) {
                r.setParent(this);
            }
            return true;
        }
        if (implementing == p) {
            Implements r = (Implements) q;
            implementing = r;
            if (r != null) {
                r.setParent(this);
            }
            return true;
        }
        count = (members == null) ? 0 : members.size();
        for (int i = 0; i < count; i++) {
            if (members.get(i) == p) {
                if (q == null) {
                    members.remove(i);
                } else {
                    MemberDeclaration r = (MemberDeclaration) q;
                    members.set(i, r);
                    r.setMemberParent(this);
                }
                return true;
            }
        }
        if (typeParameters != null) {
            int idx = typeParameters.indexOf(p);
            if (idx != -1) {
                if (q == null) {
                    typeParameters.remove(idx);
                } else {
                    TypeParameterDeclaration r = (TypeParameterDeclaration) q;
                    typeParameters.set(idx, r);
                    r.setParent(this);
                }
                return true;
            }
        }
        return false;
    }

    /**
     * Get statement container.
     *
     * @return null, if the type is not declared locally.
     */
    public StatementContainer getStatementContainer() {
        return (parent instanceof StatementContainer) ? (StatementContainer) parent : null;
    }

    /**
     * Set statement container. Must be a {@link recoder.java.StatementBlock}.
     *
     * @param p a statement container.
     */
    public void setStatementContainer(StatementContainer p) {
        parent = (StatementBlock) p;
    }

    /**
     * Get extended types.
     *
     * @return the extends.
     */
    public Extends getExtendedTypes() {
        return extending;
    }

    /**
     * Set extended types.
     *
     * @param spec an extends.
     */
    public void setExtendedTypes(Extends spec) {
        extending = spec;
    }

    /**
     * Get implemented types.
     *
     * @return the implements.
     */
    public Implements getImplementedTypes() {
        return implementing;
    }

    /**
     * Set implemented types.
     *
     * @param spec an implements.
     */
    public void setImplementedTypes(Implements spec) {
        implementing = spec;
    }

    /**
     * Classes are never strictfp.
     */
    public boolean isStrictFp() {
        return false;
    }

    /**
     * Classes are never transient.
     */
    public boolean isTransient() {
        return false;
    }

    /**
     * Classes are never volatile.
     */
    public boolean isVolatile() {
        return false;
    }

    public boolean isInterface() {
        return false;
    }

    public boolean isOrdinaryInterface() {
        return false;
    }

    public boolean isAnnotationType() {
        return false;
    }

    public boolean isEnumType() {
        return false;
    }

    public boolean isOrdinaryClass() {
        return true;
    }

    public void accept(SourceVisitor v) {
        v.visitClassDeclaration(this);
    }

    public ASTList<TypeParameterDeclaration> getTypeParameters() {
        return typeParameters;
    }

    public void setTypeParameters(ASTList<TypeParameterDeclaration> typeParameters) {
        this.typeParameters = typeParameters;
    }
}
