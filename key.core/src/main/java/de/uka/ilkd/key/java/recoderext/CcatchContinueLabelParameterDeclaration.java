/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import recoder.java.Identifier;
import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;

/**
 * A "\Continue label" parameter of a ccatch clause.
 *
 * @author Dominic Steinhöfel
 */
public class CcatchContinueLabelParameterDeclaration extends CcatchNonstandardParameterDeclaration {
    private static final long serialVersionUID = 1L;

    private Identifier label;

    public CcatchContinueLabelParameterDeclaration() {

    }

    public CcatchContinueLabelParameterDeclaration(Identifier label) {
        this.label = label;
    }

    public Identifier getLabel() {
        return label;
    }

    public void setLabel(Identifier label) {
        this.label = label;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    @Override
    public int getChildCount() {
        return (label != null) ? 1 : 0;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */

    @Override
    public ProgramElement getChildAt(int index) {
        if (label != null) {
            if (index == 0) {
                return label;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public int getChildPositionCode(ProgramElement child) {
        // role 0: label
        if (label == child) {
            return 0;
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
     * @exception ClassCastException if the new child cannot take over the role of the old one.
     */

    @Override
    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null) {
            throw new NullPointerException();
        }
        if (label == p) {
            Identifier r = (Identifier) q;
            label = r;
            if (r != null) {
                r.setParent(this);
            }
            return true;
        }
        return false;
    }

    @Override
    public void accept(SourceVisitor v) {
        if (v instanceof SourceVisitorExtended) {
            ((SourceVisitorExtended) v).visitCcatchContinueLabelParameterDeclaration(this);
        } else {
            // throw new IllegalStateException(
            // "Method 'accept' not implemented in Ccatch");
        }
    }

    @Override
    public CcatchContinueLabelParameterDeclaration deepClone() {
        return new CcatchContinueLabelParameterDeclaration();
    }

}
