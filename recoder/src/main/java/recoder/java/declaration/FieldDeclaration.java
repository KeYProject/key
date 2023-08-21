/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration;

import java.util.ArrayList;
import java.util.List;

import recoder.java.*;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/**
 * Field declaration.
 *
 * @author <TT>AutoDoc</TT>
 */

public class FieldDeclaration extends VariableDeclaration implements MemberDeclaration {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 2577966836277961911L;

    /**
     * Parent.
     */

    protected TypeDeclaration parent;

    /**
     * Field specs.
     */

    // protected RecoderProgramElementList<FieldSpecification> fieldSpecs;
    protected ASTList<FieldSpecification> fieldSpecs;

    /**
     * Field declaration.
     */

    public FieldDeclaration() {
        // nothing to do here
    }

    /**
     * Field declaration.
     *
     * @param typeRef a type reference.
     * @param name an identifier.
     */

    public FieldDeclaration(TypeReference typeRef, Identifier name) {
        setTypeReference(typeRef);
        ASTList<FieldSpecification> list = new ASTArrayList<>(1);
        list.add(getFactory().createFieldSpecification(name));
        setFieldSpecifications(list);
        makeParentRoleValid();
    }

    /**
     * Field declaration.
     *
     * @param mods a modifier mutable list.
     * @param typeRef a type reference.
     * @param name an identifier.
     * @param init an expression.
     */

    public FieldDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef,
            Identifier name, Expression init) {
        setDeclarationSpecifiers(mods);
        setTypeReference(typeRef);
        ASTList<FieldSpecification> list = new ASTArrayList<>(1);
        list.add(getFactory().createFieldSpecification(name, init));
        setFieldSpecifications(list);
        makeParentRoleValid();
    }

    /**
     * Field declaration.
     *
     * @param mods a modifier mutable list.
     * @param typeRef a type reference.
     * @param vars a variable specification mutable list.
     */

    public FieldDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef,
            ASTList<FieldSpecification> vars) {
        setDeclarationSpecifiers(mods);
        setTypeReference(typeRef);
        setFieldSpecifications(vars);
        makeParentRoleValid();
    }

    /**
     * Field declaration.
     *
     * @param proto a field declaration.
     */

    protected FieldDeclaration(FieldDeclaration proto) {
        super(proto);
        if (proto.fieldSpecs != null) {
            fieldSpecs = proto.fieldSpecs.deepClone();
        }
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public FieldDeclaration deepClone() {
        return new FieldDeclaration(this);
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
     * Get member parent.
     *
     * @return the type declaration.
     */

    public TypeDeclaration getMemberParent() {
        return parent;
    }

    /**
     * Set member parent.
     *
     * @param p a type declaration.
     */

    public void setMemberParent(TypeDeclaration p) {
        parent = p;
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (fieldSpecs != null) {
            for (int i = fieldSpecs.size() - 1; i >= 0; i -= 1) {
                fieldSpecs.get(i).setParent(this);
            }
        }
    }

    public ASTList<FieldSpecification> getFieldSpecifications() {
        return fieldSpecs;
    }

    public void setFieldSpecifications(ASTList<FieldSpecification> l) {
        fieldSpecs = l;
    }

    public List<FieldSpecification> getVariables() {
        return new ArrayList<>(fieldSpecs);
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
        if (typeReference != null) {
            result++;
        }
        if (fieldSpecs != null) {
            result += fieldSpecs.size();
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
        if (typeReference != null) {
            if (index == 0) {
                return typeReference;
            }
            index--;
        }
        if (fieldSpecs != null) {
            return fieldSpecs.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0 (IDX): modifier
        // role 1: type reference
        // role 2 (IDX): var specs
        if (declarationSpecifiers != null) {
            int index = declarationSpecifiers.indexOf(child);
            if (index >= 0) {
                return (index << 4) | 0;
            }
        }
        if (typeReference == child) {
            return 1;
        }
        if (fieldSpecs != null) {
            int index = fieldSpecs.indexOf(child);
            if (index >= 0) {
                return (index << 4) | 2;
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
        if (typeReference == p) {
            TypeReference r = (TypeReference) q;
            typeReference = r;
            if (r != null) {
                r.setParent(this);
            }
            return true;
        }

        count = (fieldSpecs == null) ? 0 : fieldSpecs.size();
        for (int i = 0; i < count; i++) {
            if (fieldSpecs.get(i) == p) {
                if (q == null) {
                    fieldSpecs.remove(i);
                } else {
                    FieldSpecification r = (FieldSpecification) q;
                    fieldSpecs.set(i, r);
                    r.setParent(this);
                }
                return true;
            }
        }
        return false;
    }

    /**
     * Test whether the declaration is final. Fields of interfaces are always final.
     */

    public boolean isFinal() {
        return (getASTParent() instanceof InterfaceDeclaration) || super.isFinal();
    }

    /**
     * Test whether the declaration is private.
     */

    public boolean isPrivate() {
        return super.isPrivate();
    }

    /**
     * Test whether the declaration is protected.
     */

    public boolean isProtected() {
        return super.isProtected();
    }

    /**
     * Test whether the declaration is public. Fields of interfaces are always public.
     */

    public boolean isPublic() {
        return (getASTParent() instanceof InterfaceDeclaration) || super.isPublic();
    }

    /**
     * Test whether the declaration is static. Fields of interfaces are always static.
     */

    public boolean isStatic() {
        return (getASTParent() instanceof InterfaceDeclaration) || super.isStatic();
    }

    /**
     * Test whether the declaration is transient.
     */

    public boolean isTransient() {
        return !(getASTParent() instanceof InterfaceDeclaration) && super.isTransient();
    }

    /**
     * Test whether the declaration is strict FP.
     */

    public boolean isStrictFp() {
        return super.isStrictFp();
    }

    public void accept(SourceVisitor v) {
        v.visitFieldDeclaration(this);
    }
}
