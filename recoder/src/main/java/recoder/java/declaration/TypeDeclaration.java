/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import recoder.abstraction.*;
import recoder.abstraction.Package;
import recoder.convenience.Naming;
import recoder.java.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.ProgramModelInfo;
import recoder.util.Debug;

/**
 * Type declaration.
 *
 * @author <TT>AutoDoc</TT>
 */
public abstract class TypeDeclaration extends JavaDeclaration implements NamedProgramElement,
        MemberDeclaration, TypeDeclarationContainer, ClassType, VariableScope, TypeScope {

    /**
     * Undefined scope tag.
     */
    protected final static Map UNDEFINED_SCOPE = new HashMap(1);
    /**
     * Name.
     */
    protected Identifier name;
    /**
     * Parent.
     */
    protected TypeDeclarationContainer parent;
    /**
     * Members.
     */
    protected ASTList<MemberDeclaration> members;
    /**
     * Service.
     */
    protected ProgramModelInfo service;
    /**
     * Scope table for types.
     */
    @SuppressWarnings("unchecked")
    protected Map<String, TypeDeclaration> name2type = UNDEFINED_SCOPE;

    /**
     * Scope table for fields.
     */
    @SuppressWarnings("unchecked")
    protected Map<String, FieldSpecification> name2field = UNDEFINED_SCOPE;

    /**
     * Type declaration.
     */
    public TypeDeclaration() {
        // nothing to do here
    }

    /**
     * Type declaration.
     *
     * @param name an identifier.
     */
    public TypeDeclaration(Identifier name) {
        setIdentifier(name);
        // makeParentRoleValid() called by subclasses' constructors
    }

    /**
     * Type declaration.
     *
     * @param mods a modifier mutable list.
     * @param name an identifier.
     */
    public TypeDeclaration(ASTList<DeclarationSpecifier> mods, Identifier name) {
        super(mods);
        setIdentifier(name);
        // makeParentRoleValid() called by subclasses' constructors
    }

    /**
     * Type declaration.
     *
     * @param proto a type declaration.
     */
    protected TypeDeclaration(TypeDeclaration proto) {
        super(proto);
        if (proto.name != null) {
            name = proto.name.deepClone();
        }
        if (proto.members != null) {
            members = proto.members.deepClone();
        }
        // makeParentRoleValid() called by subclasses' constructors
    }

    private static void updateModel() {
        factory.getServiceConfiguration().getChangeHistory().updateModel();
    }

    /**
     * Make parent role valid.
     */
    public void makeParentRoleValid() {
        if (declarationSpecifiers != null) {
            for (int i = declarationSpecifiers.size() - 1; i >= 0; i -= 1) {
                declarationSpecifiers.get(i).setParent(this);
            }
        }
        if (name != null) {
            name.setParent(this);
        }
        if (members != null) {
            for (int i = members.size() - 1; i >= 0; i -= 1) {
                members.get(i).setMemberParent(this);
            }
        }
    }

    public SourceElement getFirstElement() {
        if (declarationSpecifiers != null && !declarationSpecifiers.isEmpty()) {
            return declarationSpecifiers.get(0);
        } else {
            return this;
        }
    }

    public SourceElement getLastElement() {
        return this;
    }

    /**
     * Get name.
     *
     * @return the string.
     */
    public final String getName() {
        return (name == null) ? null : name.getText();
    }

    /**
     * Get identifier.
     *
     * @return the identifier.
     */
    public Identifier getIdentifier() {
        return name;
    }

    /**
     * Set identifier.
     *
     * @param id an identifier.
     */
    public void setIdentifier(Identifier id) {
        name = id;
    }

    /**
     * Get parent.
     *
     * @return the type declaration container.
     */
    public TypeDeclarationContainer getParent() {
        return parent;
    }

    /**
     * Set parent.
     *
     * @param p a type declaration container.
     */
    public void setParent(TypeDeclarationContainer p) {
        parent = p;
    }

    /**
     * Get member parent.
     *
     * @return the type declaration.
     */
    public TypeDeclaration getMemberParent() {
        if (parent instanceof TypeDeclaration) {
            return (TypeDeclaration) parent;
        } else {
            return null;
        }
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
     * Get AST parent.
     *
     * @return the non terminal program element.
     */
    public NonTerminalProgramElement getASTParent() {
        return parent;
    }

    /**
     * Get members.
     *
     * @return the member declaration mutable list.
     */
    public ASTList<MemberDeclaration> getMembers() {
        return members;
    }

    /**
     * Set members.
     *
     * @param list a member declaration mutable list.
     */
    public void setMembers(ASTList<MemberDeclaration> list) {
        members = list;
    }

    /**
     * Get the number of type declarations in this container.
     *
     * @return the number of type declarations.
     */
    public int getTypeDeclarationCount() {
        int count = 0;
        if (members != null) {
            for (int i = members.size() - 1; i >= 0; i -= 1) {
                if (members.get(i) instanceof TypeDeclaration) {
                    count += 1;
                }
            }
        }
        if (getTypeParameters() != null) {
            count += getTypeParameters().size();
        }
        return count;
    }

    /*
     * Return the type declaration at the specified index in this node's "virtual" type declaration
     * array. @param index an index for a type declaration. @return the type declaration with the
     * given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */
    public TypeDeclaration getTypeDeclarationAt(int index) {
        if (members != null) {
            int s = members.size();
            for (int i = 0; i < s && index >= 0; i++) {
                MemberDeclaration md = members.get(i);
                if (md instanceof TypeDeclaration) {
                    if (index == 0) {
                        return (TypeDeclaration) md;
                    }
                    index--;
                }
            }
        }
        if (getTypeParameters() != null) {
            return getTypeParameters().get(index); // may throw exception
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Test whether the declaration is final.
     */
    public boolean isFinal() {
        return super.isFinal();
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
     * Test whether the declaration is public.
     */
    public boolean isPublic() {
        return (getASTParent() instanceof InterfaceDeclaration) || super.isPublic();
    }

    /**
     * Test whether the declaration is static.
     */
    public boolean isStatic() {
        return (getASTParent() instanceof InterfaceDeclaration) || super.isStatic();
    }

    /**
     * Test whether the declaration is strictfp.
     */
    public boolean isStrictFp() {
        return super.isStrictFp();
    }

    /**
     * Test whether the declaration is abstract.
     */
    public boolean isAbstract() {
        return super.isAbstract();
    }

    public ProgramModelInfo getProgramModelInfo() {
        return service;
    }

    public void setProgramModelInfo(ProgramModelInfo service) {
        this.service = service;
    }

    public String getFullName() {
        return Naming.getFullName(this);
        /*
         * ClassTypeContainer container = getContainer(); String containerName = null; if (container
         * instanceof Method) { containerName = String.valueOf(System.identityHashCode(container));
         * container = container.getContainer(); if (container != null) { containerName =
         * Naming.dot(container.getFullName(), containerName); } } else { if (container != null) {
         * containerName = container.getFullName(); } } String name = getName(); if (name == null) {
         * name = String.valueOf(System.identityHashCode(this)); } if (containerName != null) { name
         * = Naming.dotOnDemand(containerName, name); } return name;
         */
    }

    public ClassTypeContainer getContainer() {
        if (service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (service == null) {
            Debug.error("Service not defined in TypeDeclaration " + getName());
        }
        return service.getClassTypeContainer(this);
    }

    public ClassType getContainingClassType() {
        if (service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (service == null) {
            Debug.error("Service not defined in TypeDeclaration " + getName());
        }
        ClassTypeContainer ctc = service.getClassTypeContainer(this);
        return (ctc instanceof ClassType) ? (ClassType) ctc : null;
    }

    public Package getPackage() {
        if (service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (service == null) {
            Debug.error("Service not defined in TypeDeclaration " + getName());
        }
        return service.getPackage(this);
    }

    public abstract boolean isInterface();

    public List<ClassType> getSupertypes() {
        if (service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (service == null) {
            Debug.error("Service not defined in TypeDeclaration " + getName());
        }
        return service.getSupertypes(this);
    }

    public List<ClassType> getAllSupertypes() {
        if (service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (service == null) {
            Debug.error("Service not defined in TypeDeclaration " + getName());
        }
        return service.getAllSupertypes(this);
    }

    public List<FieldSpecification> getFields() {
        if (service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (service == null) {
            Debug.error("Service not defined in TypeDeclaration " + getName());
        }
        @SuppressWarnings("unchecked")
        List<FieldSpecification> fields = (List<FieldSpecification>) service.getFields(this);
        return fields;
    }

    public List<Field> getAllFields() {
        if (service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (service == null) {
            Debug.error("Service not defined in TypeDeclaration " + getName());
        }
        return service.getAllFields(this);
    }

    public List<Method> getMethods() {
        if (service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (service == null) {
            Debug.error("Service not defined in TypeDeclaration " + getName());
        }
        return service.getMethods(this);
    }

    public List<Method> getAllMethods() {
        if (service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (service == null) {
            Debug.error("Service not defined in TypeDeclaration " + getName());
        }
        return service.getAllMethods(this);
    }

    public List<? extends Constructor> getConstructors() {
        if (service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (service == null) {
            Debug.error("Service not defined in TypeDeclaration " + getName());
        }
        return service.getConstructors(this);
    }

    public List<TypeDeclaration> getTypes() {
        if (service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (service == null) {
            Debug.error("Service not defined in TypeDeclaration " + getName());
        }
        @SuppressWarnings("unchecked")
        List<TypeDeclaration> types = (List<TypeDeclaration>) service.getTypes(this);
        return types;
    }

    public List<ClassType> getAllTypes() {
        if (service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (service == null) {
            Debug.error("Service not defined in TypeDeclaration " + getName());
        }
        return service.getAllTypes(this);
    }

    public boolean isDefinedScope() {
        return name2type != UNDEFINED_SCOPE;
    }

    @SuppressWarnings("unchecked")
    public void setDefinedScope(boolean defined) {
        if (!defined) {
            name2type = UNDEFINED_SCOPE;
            name2field = UNDEFINED_SCOPE;
        } else {
            name2type = null;
            name2field = null;
        }
    }

    public List<TypeDeclaration> getTypesInScope() {
        if (name2type == null || name2type.isEmpty()) {
            return new ArrayList<>(0);
        }
        List<TypeDeclaration> res = new ArrayList<>();
        for (TypeDeclaration td : name2type.values()) {
            res.add(td);
        }
        return res;
    }

    public ClassType getTypeInScope(String tname) {
        Debug.assertNonnull(tname);
        if (name2type == null) {
            return null;
        }
        return name2type.get(tname);
    }

    public void addTypeToScope(ClassType type, String tname) {
        Debug.assertNonnull(type, tname);
        if (name2type == null || name2type == UNDEFINED_SCOPE) {
            name2type = new HashMap<>();
        }
        name2type.put(tname, (TypeDeclaration) type);
    }

    public void removeTypeFromScope(String tname) {
        Debug.assertNonnull(tname);
        if (name2type == null || name2type == UNDEFINED_SCOPE) {
            return;
        }
        name2type.remove(tname);
    }

    public List<FieldSpecification> getFieldsInScope() {
        if (name2field == null || name2field.isEmpty()) {
            return new ASTArrayList<>(0);
        }
        ASTList<FieldSpecification> res = new ASTArrayList<>();
        for (FieldSpecification fs : name2field.values()) {
            res.add(fs);
        }
        return res;
    }

    public List<? extends VariableSpecification> getVariablesInScope() {
        return getFieldsInScope();
    }

    public VariableSpecification getVariableInScope(String tname) {
        Debug.assertNonnull(tname);
        if (name2field == null) {
            return null;
        }
        return name2field.get(tname);
    }

    public void addVariableToScope(VariableSpecification var) {
        Debug.assertBoolean(var instanceof FieldSpecification
                || (var instanceof EnumConstantSpecification && this instanceof EnumDeclaration));
        if (name2field == null || name2field == UNDEFINED_SCOPE) {
            name2field = new HashMap<>();
        }
        name2field.put(var.getName(), (FieldSpecification) var);
    }

    public void removeVariableFromScope(String tname) {
        Debug.assertNonnull(tname);
        if (name2field == null || name2field == UNDEFINED_SCOPE) {
            return;
        }
        name2field.remove(tname);
    }

    public abstract ASTList<TypeParameterDeclaration> getTypeParameters();

    @Override
    public String toString() {
        return getClass().getSimpleName() + " " + getFullName();
    }

    public abstract TypeDeclaration deepClone();

}
