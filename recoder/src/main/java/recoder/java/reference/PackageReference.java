/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.reference;

import recoder.java.*;

/**
 * Package reference.
 *
 * @author <TT>AutoDoc</TT>
 */

public class PackageReference extends JavaNonTerminalProgramElement
        implements TypeReferenceInfix, PackageReferenceContainer {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -4209613321578432317L;

    /**
     * Prefix.
     */

    protected ReferencePrefix prefix;

    /**
     * Parent.
     */

    protected PackageReferenceContainer parent;

    /**
     * Name.
     */

    protected Identifier name;

    /**
     * Package reference.
     */

    public PackageReference() {
        // nothing to do
    }

    /**
     * Package reference.
     *
     * @param id an identifier.
     */

    public PackageReference(Identifier id) {
        setIdentifier(id);
        makeParentRoleValid();
    }

    /**
     * Package reference.
     *
     * @param path a package reference.
     * @param id an identifier.
     */

    public PackageReference(PackageReference path, Identifier id) {
        setReferencePrefix(path);
        setIdentifier(id);
        makeParentRoleValid();
    }

    /**
     * Package reference.
     *
     * @param proto a package reference.
     */

    protected PackageReference(PackageReference proto) {
        super(proto);
        if (proto.prefix != null) {
            prefix = (ReferencePrefix) proto.prefix.deepClone();
        }
        if (proto.name != null) {
            name = proto.name.deepClone();
        }
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public PackageReference deepClone() {
        return new PackageReference(this);
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (prefix != null) {
            prefix.setReferenceSuffix(this);
        }
        if (name != null) {
            name.setParent(this);
        }
    }

    public SourceElement getFirstElement() {
        return (prefix == null) ? name : prefix.getFirstElement();
    }

    public SourceElement getLastElement() {
        return name;
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
        if (prefix != null) {
            result++;
        }
        if (name != null) {
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
        if (prefix != null) {
            if (index == 0) {
                return prefix;
            }
            index--;
        }
        if (name != null) {
            if (index == 0) {
                return name;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0: prefix
        // role 1: name
        if (prefix == child) {
            return 0;
        }
        if (name == child) {
            return 1;
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
        if (prefix == p) {
            PackageReference r = (PackageReference) q;
            prefix = r;
            if (r != null) {
                r.setParent(this);
            }
            return true;
        }
        if (name == p) {
            Identifier r = (Identifier) q;
            name = r;
            if (r != null) {
                r.setParent(this);
            }
            return true;
        }

        return false;
    }

    /**
     * Set package specification.
     *
     * @param parent a package specification.
     */

    public void setParent(PackageReferenceContainer parent) {
        this.parent = parent;
    }

    /**
     * Get reference prefix.
     *
     * @return the reference prefix.
     */

    public ReferencePrefix getReferencePrefix() {
        return prefix;
    }

    /**
     * Set reference prefix.
     *
     * @param prefix a reference prefix.
     */

    public void setReferencePrefix(ReferencePrefix prefix) {
        this.prefix = prefix;
    }

    /**
     * Get the package reference.
     *
     * @return the package reference.
     */

    public PackageReference getPackageReference() {
        return (prefix instanceof PackageReference) ? (PackageReference) prefix : null;
    }

    /**
     * Get reference suffix.
     *
     * @return the reference suffix.
     */

    public ReferenceSuffix getReferenceSuffix() {
        return (parent instanceof ReferenceSuffix) ? (ReferenceSuffix) parent : null;
    }

    /**
     * Set reference suffix. Must be a PackageReferenceContainer.
     *
     * @param x a reference suffix.
     */

    public void setReferenceSuffix(ReferenceSuffix x) {
        parent = (PackageReferenceContainer) x;
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

    public void accept(SourceVisitor v) {
        v.visitPackageReference(this);
    }
}
