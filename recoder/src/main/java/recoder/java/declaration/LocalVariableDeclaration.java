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
 * Local variable declaration.
 *
 * @author <TT>AutoDoc</TT>
 */

public class LocalVariableDeclaration extends VariableDeclaration implements LoopInitializer {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -504401927803552291L;

    /**
     * Parent.
     */

    protected StatementContainer parent;

    /**
     * Var specs.
     */

    protected ASTList<VariableSpecification> varSpecs;

    /**
     * Local variable declaration.
     */

    public LocalVariableDeclaration() {
        // nothing to do here
    }

    /**
     * Local variable declaration.
     *
     * @param typeRef a type reference.
     * @param name an identifier.
     */

    public LocalVariableDeclaration(TypeReference typeRef, Identifier name) {
        setTypeReference(typeRef);
        ASTList<VariableSpecification> list = new ASTArrayList<>(1);
        list.add(getFactory().createVariableSpecification(name));
        setVariableSpecifications(list);
        makeParentRoleValid();
    }

    /**
     * Local variable declaration.
     *
     * @param mods a modifier mutable list.
     * @param typeRef a type reference.
     * @param vars a variable specification mutable list.
     */

    public LocalVariableDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef,
            ASTList<VariableSpecification> vars) {
        setDeclarationSpecifiers(mods);
        setTypeReference(typeRef);
        setVariableSpecifications(vars);
        makeParentRoleValid();
    }

    /**
     * Local variable declaration.
     *
     * @param mods a modifier mutable list.
     * @param typeRef a type reference.
     * @param name an identifier.
     * @param init an expression.
     */

    public LocalVariableDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef,
            Identifier name, Expression init) {
        setDeclarationSpecifiers(mods);
        setTypeReference(typeRef);
        ASTList<VariableSpecification> list = new ASTArrayList<>(1);
        list.add(getFactory().createVariableSpecification(name, init));
        setVariableSpecifications(list);
        makeParentRoleValid();
    }

    /**
     * Local variable declaration.
     *
     * @param proto a local variable declaration.
     */

    protected LocalVariableDeclaration(LocalVariableDeclaration proto) {
        super(proto);
        if (proto.varSpecs != null) {
            varSpecs = proto.varSpecs.deepClone();
        }
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public LocalVariableDeclaration deepClone() {
        return new LocalVariableDeclaration(this);
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (varSpecs != null) {
            for (int i = varSpecs.size() - 1; i >= 0; i -= 1) {
                varSpecs.get(i).setParent(this);
            }
        }
    }

    public ASTList<VariableSpecification> getVariableSpecifications() {
        return varSpecs;
    }

    public void setVariableSpecifications(ASTList<VariableSpecification> l) {
        varSpecs = l;
    }

    public List<VariableSpecification> getVariables() {
        return new ArrayList<>(varSpecs);
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
        if (varSpecs != null) {
            result += varSpecs.size();
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
        if (varSpecs != null) {
            return varSpecs.get(index);
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
        if (varSpecs != null) {
            int index = varSpecs.indexOf(child);
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

        count = (varSpecs == null) ? 0 : varSpecs.size();
        for (int i = 0; i < count; i++) {
            if (varSpecs.get(i) == p) {
                if (q == null) {
                    varSpecs.remove(i);
                } else {
                    VariableSpecification r = (VariableSpecification) q;
                    varSpecs.set(i, r);
                    r.setParent(this);
                }
                return true;
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
     * Get statement container.
     *
     * @return the statement container.
     */

    public StatementContainer getStatementContainer() {
        return parent;
    }

    /**
     * Set statement container.
     *
     * @param c a statement container.
     */

    public void setStatementContainer(StatementContainer c) {
        parent = c;
    }

    /**
     * Local variables are never private.
     */

    public boolean isPrivate() {
        return false;
    }

    /**
     * Local variables are never protected..
     */

    public boolean isProtected() {
        return false;
    }

    /**
     * Local variables are never "public".
     */

    public boolean isPublic() {
        return false;
    }

    /**
     * Local variables are never static.
     */

    public boolean isStatic() {
        return false;
    }

    /**
     * Local variables are never transient.
     */

    public boolean isTransient() {
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitLocalVariableDeclaration(this);
    }
}
