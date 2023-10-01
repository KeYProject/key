/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration;

import java.util.ArrayList;
import java.util.List;

import recoder.java.*;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTList;

/**
 * Formal parameters require a VariableSpecificationList of size() <= 1 (size() == 0 for abstract
 * methods) without initializer (for Java).
 */

public class ParameterDeclaration extends VariableDeclaration {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -7820198330917949601L;

    /**
     * Parent.
     */

    protected ParameterContainer parent;

    /**
     * Var spec.
     */

    protected VariableSpecification varSpec;

    protected boolean varArgParameter;

    /**
     * Parameter declaration.
     */

    public ParameterDeclaration() {
        // nothing to do here
    }

    /**
     * Parameter declaration.
     *
     * @param typeRef a type reference.
     * @param name an identifier.
     */

    public ParameterDeclaration(TypeReference typeRef, Identifier name) {
        setTypeReference(typeRef);
        setVariableSpecification(getFactory().createVariableSpecification(name));
        makeParentRoleValid();
    }

    /**
     * Parameter declaration.
     *
     * @param mods a modifier mutable list.
     * @param typeRef a type reference.
     * @param name an identifier.
     */

    public ParameterDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef,
            Identifier name) {
        setDeclarationSpecifiers(mods);
        setTypeReference(typeRef);
        setVariableSpecification(getFactory().createVariableSpecification(name));
        makeParentRoleValid();
    }

    /**
     * Parameter declaration.
     *
     * @param proto a parameter declaration.
     */

    protected ParameterDeclaration(ParameterDeclaration proto) {
        super(proto);
        varSpec = proto.varSpec.deepClone();
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public ParameterDeclaration deepClone() {
        return new ParameterDeclaration(this);
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (varSpec != null) {
            varSpec.setParent(this);
        }
    }

    public VariableSpecification getVariableSpecification() {
        return varSpec;
    }

    public void setVariableSpecification(VariableSpecification vs) {
        varSpec = vs;
    }

    public List<VariableSpecification> getVariables() {
        List<VariableSpecification> res = new ArrayList<>(1);
        res.add(varSpec);
        return res;
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
        if (varSpec != null) {
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
        if (varSpec != null) {
            if (index == 0) {
                return varSpec;
            }
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
        if (varSpec == child) {
            return 2;
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
        if (varSpec == p) {
            VariableSpecification r = (VariableSpecification) q;
            varSpec = r;
            if (r != null) {
                r.setParent(this);
            }
            return true;
        }
        return false;
    }

    /**
     * Get parameter container.
     *
     * @return the parameter container.
     */

    public ParameterContainer getParameterContainer() {
        return parent;
    }

    /**
     * Set parameter container.
     *
     * @param c a parameter container.
     */

    public void setParameterContainer(ParameterContainer c) {
        parent = c;
    }

    /**
     * Parameters are never private.
     */

    public boolean isPrivate() {
        return false;
    }

    /**
     * Parameters are never protected..
     */

    public boolean isProtected() {
        return false;
    }

    /**
     * Parameters are never "public".
     */

    public boolean isPublic() {
        return false;
    }

    /**
     * Parameters are never static.
     */

    public boolean isStatic() {
        return false;
    }

    /**
     * Parameters are never transient.
     */

    public boolean isTransient() {
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitParameterDeclaration(this);
    }

    public boolean isVarArg() {
        return varArgParameter;
    }

    public void setVarArg(boolean varArg) {
        this.varArgParameter = varArg;
    }

}
