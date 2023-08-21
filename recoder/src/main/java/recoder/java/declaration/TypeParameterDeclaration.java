/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration;

import recoder.ModelException;
import recoder.abstraction.ClassType;
import recoder.abstraction.TypeParameter;
import recoder.convenience.Naming;
import recoder.java.Identifier;
import recoder.java.ProgramElement;
import recoder.java.SourceElement;
import recoder.java.SourceVisitor;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceContainer;
import recoder.list.generic.ASTList;

/**
 * @author Tobias Gutzmann
 */
public class TypeParameterDeclaration extends TypeDeclaration
        implements TypeReferenceContainer, TypeParameter {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -6480521507901415027L;

    protected ASTList<TypeReference> bound;

    /**
     *
     */
    public TypeParameterDeclaration() {
        super();
    }

    public TypeParameterDeclaration(Identifier name, ASTList<TypeReference> bound) {
        super(name);
        this.bound = bound;
        makeParentRoleValid();
    }

    /**
     * @param proto
     */
    protected TypeParameterDeclaration(TypeParameterDeclaration proto) {
        super(proto);
        if (proto.bound != null) {
            bound = proto.bound.deepClone();
        }
        makeParentRoleValid();
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.reference.TypeReferenceContainer#getTypeReferenceCount()
     */
    public int getTypeReferenceCount() {
        return bound == null ? 0 : bound.size();
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.reference.TypeReferenceContainer#getTypeReferenceAt(int)
     */
    public TypeReference getTypeReferenceAt(int index) {
        if (index == 0 && bound != null) {
            return bound.get(index);
        }
        throw new ArrayIndexOutOfBoundsException(index);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.NonTerminalProgramElement#getChildCount()
     */
    public int getChildCount() {
        return (name != null ? 1 : 0) + (bound != null ? bound.size() : 0);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.NonTerminalProgramElement#getChildAt(int)
     */
    public ProgramElement getChildAt(int index) {
        if (name != null) {
            if (index == 0) {
                return name;
            }
            index--;
        }
        if (bound != null) {
            return bound.get(index); // may throw exception
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.NonTerminalProgramElement#getChildPositionCode(recoder.java.ProgramElement)
     */
    public int getChildPositionCode(ProgramElement child) {
        // 0 : name
        // 1(idx) : bound
        if (child == name) {
            return 0;
        }
        int idx = bound.indexOf(child);
        if (idx != -1) {
            return (idx << 4) | 1;
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
        if (p == name) {
            name = (Identifier) q;
            if (name != null) {
                name.setParent(this);
            }
            return true;
        }
        if (bound != null) {
            int idx = bound.indexOf(p);
            if (idx != -1) {
                if (q == null) {
                    bound.remove(idx);
                } else {
                    TypeReference tr = (TypeReference) q;
                    bound.set(idx, tr);
                    tr.setParent(this);
                }
            }
            return true;
        }
        return false;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.SourceElement#accept(recoder.java.SourceVisitor)
     */
    public void accept(SourceVisitor v) {
        v.visitTypeParameter(this);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.SourceElement#deepClone()
     */
    public TypeParameterDeclaration deepClone() {
        return new TypeParameterDeclaration(this);
    }

    @Override
    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (bound != null) {
            for (TypeReference tr : bound) {
                tr.setParent(this);
            }
        }
    }

    @Override
    public void validate() throws ModelException {
        if (members != null && members.size() != 0) {
            throw new ModelException("No members allowed in TypeParameter");
        }
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
        return false;
    }

    @Override
    public ASTList<TypeParameterDeclaration> getTypeParameters() {
        return null;
    }

    public ASTList<TypeReference> getBounds() {
        return bound;
    }

    public String getParameterName() {
        return getName();
    }

    public int getBoundCount() {
        return bound == null ? 0 : bound.size();
    }

    public String getBoundName(int boundidx) {
        return Naming.toPathName(bound.get(boundidx));
    }

    public ASTList<TypeArgumentDeclaration> getBoundTypeArguments(int boundidx) {
        return bound.get(boundidx).getTypeArguments();
    }

    public boolean equals(Object o) {
        return TypeParameter.EqualsImplementor.equals(this, o);
    }

    public void setBound(ASTList<TypeReference> bound) {
        this.bound = bound;
    }

    @Override
    public SourceElement getFirstElement() {
        return name;
    }

    @Override
    public SourceElement getLastElement() {
        if (bound != null) {
            return bound.get(bound.size() - 1);
        }
        return name;
    }

    @Override
    public ClassType getTypeInScope(@SuppressWarnings("unused") String tname) {
        return null;
    }

    @Override
    public void addTypeToScope(@SuppressWarnings("unused") ClassType type,
            @SuppressWarnings("unused") String tname) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void addVariableToScope(@SuppressWarnings("unused") VariableSpecification var) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void removeTypeFromScope(@SuppressWarnings("unused") String tname) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void removeVariableFromScope(@SuppressWarnings("unused") String tname) {
        throw new UnsupportedOperationException();
    }
}
