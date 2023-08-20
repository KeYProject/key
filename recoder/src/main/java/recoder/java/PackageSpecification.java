/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java;

import recoder.java.declaration.AnnotationUseSpecification;
import recoder.java.reference.PackageReference;
import recoder.java.reference.PackageReferenceContainer;
import recoder.list.generic.ASTList;

/**
 * Package specification.
 *
 * @author <TT>AutoDoc</TT>
 */

public class PackageSpecification extends JavaNonTerminalProgramElement
        implements PackageReferenceContainer {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -6415275246661492494L;

    /**
     * Parent.
     */

    protected CompilationUnit parent;

    /**
     * Reference.
     */

    protected PackageReference reference;

    protected ASTList<AnnotationUseSpecification> annotations;

    /**
     * Package specification.
     */

    public PackageSpecification() {
        // nothing to do here
    }

    /**
     * Package specification.
     *
     * @param pkg a package reference.
     */

    public PackageSpecification(PackageReference pkg) {
        setPackageReference(pkg);
        makeParentRoleValid();
    }

    /**
     * Package specification.
     *
     * @param proto a package specification.
     */

    protected PackageSpecification(PackageSpecification proto) {
        super(proto);
        if (proto.reference != null) {
            reference = proto.reference.deepClone();
        }
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public PackageSpecification deepClone() {
        return new PackageSpecification(this);
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        reference.setParent(this);
        if (annotations != null) {
            for (AnnotationUseSpecification annotation : annotations) {
                annotation.setParent(this);
            }
        }
    }

    public SourceElement getLastElement() {
        return reference;
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
        if (reference != null) {
            result++;
        }
        if (annotations != null) {
            result += annotations.size();
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
        if (reference != null) {
            if (index == 0) {
                return reference;
            }
            index--;
        }
        return annotations.get(index);
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0: reference
        // role 1 (idx): annotation use
        if (child == reference) {
            return 0;
        }
        if (annotations != null) {
            int idx = annotations.indexOf(child);
            if (idx != -1) {
                return (idx << 4) | 1;
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
        if (reference == p) {
            PackageReference r = (PackageReference) q;
            reference = r;
            if (r != null) {
                r.setParent(this);
            }
            return true;
        }
        int idx = annotations.indexOf(p);
        if (idx != -1) {
            AnnotationUseSpecification aus = (AnnotationUseSpecification) q;
            annotations.set(idx, aus);
            if (aus != null) {
                aus.setParent(this);
            }
            return true;
        }
        return false;
    }

    /**
     * Get parent.
     *
     * @return the compilation unit.
     */

    public CompilationUnit getParent() {
        return parent;
    }

    /**
     * Set parent.
     *
     * @param u a compilation unit.
     */

    public void setParent(CompilationUnit u) {
        parent = u;
    }

    /**
     * Get package reference.
     *
     * @return the package reference.
     */

    public PackageReference getPackageReference() {
        return reference;
    }

    /**
     * Set package reference.
     *
     * @param ref a package reference.
     */

    public void setPackageReference(PackageReference ref) {
        reference = ref;
    }

    public void accept(SourceVisitor v) {
        v.visitPackageSpecification(this);
    }

    public ASTList<AnnotationUseSpecification> getAnnotations() {
        return annotations;
    }

    public void setAnnotations(ASTList<AnnotationUseSpecification> annotations) {
        this.annotations = annotations;
    }
}
