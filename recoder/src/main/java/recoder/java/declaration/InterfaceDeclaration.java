/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration;

import recoder.java.Identifier;
import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.list.generic.ASTList;

/**
 * Interface declaration.
 *
 * @author <TT>AutoDoc</TT>
 */

public class InterfaceDeclaration extends TypeDeclaration {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -9140653869908200337L;

    /**
     * Extending.
     */

    protected Extends extending;

    /**
     * Type Parameters (Java 5)
     */
    protected ASTList<TypeParameterDeclaration> typeParameters;


    /**
     * Interface declaration.
     */

    public InterfaceDeclaration() {
        // nothing to do
    }

    /**
     * Construct a new outer or member interface class.
     */

    public InterfaceDeclaration(ASTList<DeclarationSpecifier> modifiers, Identifier name,
            Extends extended, ASTList<MemberDeclaration> members,
            ASTList<TypeParameterDeclaration> typeParameters) {
        super(modifiers, name);
        setExtendedTypes(extended);
        setMembers(members);
        setTypeParameters(typeParameters);
        makeParentRoleValid();
    }

    public InterfaceDeclaration(ASTList<DeclarationSpecifier> modifiers, Identifier name,
            Extends extended, ASTList<MemberDeclaration> members) {
        this(modifiers, name, extended, members, null);
    }

    /**
     * Interface declaration.
     *
     * @param proto an interface declaration.
     */

    protected InterfaceDeclaration(InterfaceDeclaration proto) {
        super(proto);
        if (proto.extending != null) {
            extending = proto.extending.deepClone();
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

    public InterfaceDeclaration deepClone() {
        return new InterfaceDeclaration(this);
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (extending != null) {
            extending.setParent(this);
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
        if (members != null) {
            len = members.size();
            if (len > index) {
                return members.get(index);
            }
            index -= len;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0 (IDX): modifier
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
     * Interfaces are always abstract.
     */

    public boolean isAbstract() {
        return true;
    }

    /**
     * Interfaces are never native.
     */

    public boolean isNative() {
        return false;
    }

    /**
     * Interfaces are never protected.
     */

    public boolean isProtected() {
        return false;
    }

    /**
     * Interfaces are never private.
     */

    public boolean isPrivate() {
        return false;
    }

    /**
     * Interfaces are never strictfp.
     */

    public boolean isStrictFp() {
        return false;
    }

    /**
     * Interfaces are never synchronized.
     */

    public boolean isSynchronized() {
        return false;
    }

    /**
     * Interfaces are never transient.
     */

    public boolean isTransient() {
        return false;
    }

    /**
     * Interfaces are never volatile.
     */

    public boolean isVolatile() {
        return false;
    }

    public boolean isInterface() {
        return true;
    }

    public boolean isOrdinaryInterface() {
        return true;
    }

    public boolean isAnnotationType() {
        return false;
    }

    public boolean isEnumType() {
        return false;
    }

    public boolean isOrdinaryClass() {
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitInterfaceDeclaration(this);
    }

    public ASTList<TypeParameterDeclaration> getTypeParameters() {
        return typeParameters;
    }

    public void setTypeParameters(ASTList<TypeParameterDeclaration> typeParameters) {
        this.typeParameters = typeParameters;
    }
}
