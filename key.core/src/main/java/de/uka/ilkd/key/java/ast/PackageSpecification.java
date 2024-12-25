/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast;

import de.uka.ilkd.key.java.ast.reference.PackageReference;
import de.uka.ilkd.key.java.ast.reference.PackageReferenceContainer;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * Package specification. taken from COMPOST and changed to achieve an immutable structure
 */
public class PackageSpecification extends JavaNonTerminalProgramElement
        implements PackageReferenceContainer {


    /**
     * Reference.
     */
    protected final PackageReference reference;

    public PackageSpecification(PackageReference reference) {
        this(null, null, reference);
    }

    public PackageSpecification(@Nullable PositionInfo pi, @Nullable List<Comment> c, PackageReference packageReference) {
        super(pi, c);
        this.reference = packageReference;
    }

    public SourceElement getLastElement() {
        return reference;
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
        return result;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index
     *        an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException
     *            if <tt>index</tt> is out of bounds
     */

    public ProgramElement getChildAt(int index) {
        if (reference != null) {
            if (index == 0) {
                return reference;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
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
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnPackageSpecification(this);
    }
}
