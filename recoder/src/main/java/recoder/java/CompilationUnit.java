/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import recoder.abstraction.ClassType;
import recoder.io.DataLocation;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.TypeDeclarationContainer;
import recoder.list.generic.ASTList;
import recoder.util.Debug;

/**
 * A node representing a single source file containing {@link TypeDeclaration}s and an optional
 * {@link PackageSpecification}and an optional set of {@link Import}s. In Java, any source file may
 * contain at most one public class type definition.
 *
 * @author AL
 * @author <TT>AutoDoc</TT>
 */

public class CompilationUnit extends JavaNonTerminalProgramElement
        implements TypeDeclarationContainer, TypeScope {

    /**
     * Undefined scope tag.
     */

    protected final static Map UNDEFINED_SCOPE = new HashMap(1);
    /**
     *
     */
    private static final long serialVersionUID = -1511486506045179278L;
    /**
     * Current data location.
     */

    protected DataLocation location;
    /**
     * Original data location.
     */

    protected DataLocation originalLocation;
    /**
     * Package spec.
     */

    protected PackageSpecification packageSpec;
    /**
     * Imports.
     */

    protected ASTList<Import> imports;
    /**
     * Type declarations.
     */

    protected ASTList<TypeDeclaration> typeDeclarations;
    /**
     * Scope table.
     */

    @SuppressWarnings("unchecked")
    protected Map<String, ClassType> name2type = UNDEFINED_SCOPE;

    /**
     * Compilation unit.
     */

    public CompilationUnit() {
        makeParentRoleValid();
    }

    /**
     * Compilation unit.
     *
     * @param pkg a package specification.
     * @param imports an import mutable list.
     * @param typeDeclarations a type declaration mutable list.
     */

    public CompilationUnit(PackageSpecification pkg, ASTList<Import> imports,
            ASTList<TypeDeclaration> typeDeclarations) {
        setPackageSpecification(pkg);
        setImports(imports);
        setDeclarations(typeDeclarations);
        makeParentRoleValid();
    }

    /**
     * Compilation unit. Does not copy the data location.
     *
     * @param proto a compilation unit.
     */

    protected CompilationUnit(CompilationUnit proto) {
        super(proto);
        if (proto.packageSpec != null) {
            packageSpec = proto.packageSpec.deepClone();
        }
        if (proto.imports != null) {
            imports = proto.imports.deepClone();
        }
        if (proto.typeDeclarations != null) {
            typeDeclarations = proto.typeDeclarations.deepClone();
        }
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public CompilationUnit deepClone() {
        return new CompilationUnit(this);
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (packageSpec != null) {
            packageSpec.setParent(this);
        }
        if (imports != null) {
            for (int i = imports.size() - 1; i >= 0; i -= 1) {
                imports.get(i).setParent(this);
            }
        }
        if (typeDeclarations != null) {
            for (int i = typeDeclarations.size() - 1; i >= 0; i -= 1) {
                typeDeclarations.get(i).setParent(this);
            }
        }
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
        if (packageSpec == p) {
            PackageSpecification r = (PackageSpecification) q;
            packageSpec = r;
            if (r != null) {
                r.setParent(this);
            }
            return true;
        }
        count = (imports == null) ? 0 : imports.size();
        for (int i = 0; i < count; i++) {
            if (imports.get(i) == p) {
                if (q == null) {
                    imports.remove(i);
                } else {
                    Import r = (Import) q;
                    imports.set(i, r);
                    r.setParent(this);
                }
                return true;
            }
        }
        count = (typeDeclarations == null) ? 0 : typeDeclarations.size();
        for (int i = 0; i < count; i++) {
            if (typeDeclarations.get(i) == p) {
                if (q == null) {
                    typeDeclarations.remove(i);
                } else {
                    TypeDeclaration r = (TypeDeclaration) q;
                    typeDeclarations.set(i, r);
                    r.setParent(this);
                }
                return true;
            }
        }
        return false;
    }

    public SourceElement getFirstElement() {
        return (getChildCount() > 0) ? getChildAt(0).getFirstElement() : this;
    }

    public SourceElement getLastElement() {
        return (typeDeclarations != null && !typeDeclarations.isEmpty())
                ? typeDeclarations.get(typeDeclarations.size() - 1).getLastElement()
                : this;
    }

    /**
     * Get name of the unit. The name is empty if no data location is set; otherwise, the name of
     * the current data location is returned.
     *
     * @return the name of this compilation unit.
     * @see #getDataLocation()
     */

    public String getName() {
        return (location == null) ? "" : location.toString();
    }

    /**
     * A compilation unit has no syntactical parent
     */

    public NonTerminalProgramElement getASTParent() {
        return null;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        int result = 0;
        if (packageSpec != null) {
            result++;
        }
        if (imports != null) {
            result += imports.size();
        }
        if (typeDeclarations != null) {
            result += typeDeclarations.size();
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
        if (packageSpec != null) {
            if (index == 0) {
                return packageSpec;
            }
            index--;
        }
        if (imports != null) {
            len = imports.size();
            if (len > index) {
                return imports.get(index);
            }
            index -= len;
        }
        if (typeDeclarations != null) {
            return typeDeclarations.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0: package spec
        // role 1 (IDX): import
        // role 2 (IDX): declarations
        if (child == packageSpec) {
            return 0;
        }
        if (imports != null) {
            int index = imports.indexOf(child);
            if (index >= 0) {
                return (index << 4) | 1;
            }
        }
        if (typeDeclarations != null) {
            int index = typeDeclarations.indexOf(child);
            if (index >= 0) {
                return (index << 4) | 2;
            }
        }
        return -1;
    }

    /**
     * Gets the current data location.
     *
     * @return the data location.
     */

    public DataLocation getDataLocation() {
        return location;
    }

    /**
     * Sets the current data location. If the data location has been <CODE>null
     * </CODE>, the location also becomes the new original location.
     *
     * @param location a data location.
     */

    public void setDataLocation(DataLocation location) {
        if (this.location == null) {
            originalLocation = location;
        }
        this.location = location;
    }

    /**
     * Gets the original data location.
     *
     * @return the original data location.
     */

    public DataLocation getOriginalDataLocation() {
        return originalLocation;
    }

    /**
     * Get imports.
     *
     * @return the import mutable list.
     */

    public ASTList<Import> getImports() {
        return imports;
    }

    /**
     * Set imports.
     *
     * @param list an import mutable list.
     */

    public void setImports(ASTList<Import> list) {
        imports = list;
    }

    /**
     * Get package specification.
     *
     * @return the package specification.
     */

    public PackageSpecification getPackageSpecification() {
        return packageSpec;
    }

    /**
     * Set package specification.
     *
     * @param p a package specification.
     */

    public void setPackageSpecification(PackageSpecification p) {
        packageSpec = p;
    }

    /**
     * Get the number of type declarations in this container.
     *
     * @return the number of type declarations.
     */

    public int getTypeDeclarationCount() {
        return (typeDeclarations != null) ? typeDeclarations.size() : 0;
    }

    /*
     * Return the type declaration at the specified index in this node's "virtual" type declaration
     * array. @param index an index for a type declaration. @return the type declaration with the
     * given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public TypeDeclaration getTypeDeclarationAt(int index) {
        if (typeDeclarations != null) {
            return typeDeclarations.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get declarations.
     *
     * @return the type declaration mutable list.
     */

    public ASTList<TypeDeclaration> getDeclarations() {
        return typeDeclarations;
    }

    /**
     * Set declarations.
     *
     * @param list a type declaration mutable list.
     */

    public void setDeclarations(ASTList<TypeDeclaration> list) {
        typeDeclarations = list;
    }

    /**
     * Gets the primary type declaration of the compilation unit. The primary declaration is the
     * first declaration of the unit, or the single public declaration. If there is no unambiguous
     * primary declaration, this method returns <CODE>null</CODE>.
     */

    public TypeDeclaration getPrimaryTypeDeclaration() {
        TypeDeclaration res = null;
        int s = typeDeclarations.size();
        for (TypeDeclaration t : typeDeclarations) {
            if (t.isPublic()) {
                if (res == null || !res.isPublic()) {
                    res = t;
                } else {
                    res = null;
                    break;
                }
            } else {
                if (res == null) {
                    res = t;
                }
            }
        }
        return res;
    }

    public boolean isDefinedScope() {
        return name2type != UNDEFINED_SCOPE;
    }

    @SuppressWarnings("unchecked")
    public void setDefinedScope(boolean defined) {
        if (!defined) {
            name2type = UNDEFINED_SCOPE;
        } else {
            name2type = null;
        }
    }

    public List<ClassType> getTypesInScope() {
        if (name2type == null || name2type.isEmpty()) {
            return new ArrayList<>(0);
        }
        List<ClassType> res = new ArrayList<>();
        for (ClassType ct : name2type.values()) {
            res.add(ct);
        }
        return res;
    }

    public ClassType getTypeInScope(String name) {
        Debug.assertNonnull(name);
        if (name2type == null || name2type == UNDEFINED_SCOPE) {
            return null;
        }
        return name2type.get(name);
    }

    public void addTypeToScope(ClassType type, String name) {
        Debug.assertNonnull(type, name);
        if (name2type == null || name2type == UNDEFINED_SCOPE) {
            name2type = new HashMap<>();
        }
        name2type.put(name, type);
    }

    public void removeTypeFromScope(String name) {
        Debug.assertNonnull(name);
        if (name2type == null || name2type == UNDEFINED_SCOPE) {
            return;
        }
        name2type.remove(name);
    }

    public void accept(SourceVisitor v) {
        v.visitCompilationUnit(this);
    }

    @Override
    public CompilationUnit compilationUnit() {
        return this;
    }
}
