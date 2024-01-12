/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java;

import recoder.ModelException;

/**
 * Non terminal program element.
 *
 * @author <TT>AutoDoc</TT>
 */

public interface NonTerminalProgramElement extends ProgramElement {

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    int getChildCount();

    /**
     * Returns the child at the specified index in this node's "virtual" child array.
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */
    ProgramElement getChildAt(int index);

    /**
     * Returns the index of the given child, or <CODE>-1</CODE> if there is no such child. The child
     * is searched for by identity: <CODE>
     * getChildAt(getIndexOfChild(x)) == x</CODE>.
     *
     * @param child the exact child to look for.
     * @return the index of the given child, or <CODE>-1</CODE>.
     */
    int getIndexOfChild(ProgramElement child);

    /**
     * Returns the positional code of the given child, or <CODE>-1</CODE> if there is no such child.
     * The result contains an encoding of the relative position of the child as well as the role it
     * has been playing in this parent element. This information is required internally for proper
     * undo of transformations and is to be delivered to the detached method of the ChangeHistory.
     *
     * @param child the exact child to look for.
     * @return the positional code of the given child, or <CODE>-1</CODE>.
     * @see recoder.service.ChangeHistory#detached
     */
    int getChildPositionCode(ProgramElement child);

    /**
     * Extracts the index of a child from its position code.
     * <p>
     * This method does not return the child index as received by getIndexOfChild(), but rather the
     * index within internal data structure representation.
     * <p>
     * Therefore it is common that <code>getIndexOfChild(getChildPositionCode(aChild))
     * != getIndexOfChild(aChild)</code>
     * <p>
     * This method is deprecated as of 0.75
     *
     * @param positionCode the position code.
     * @return the index of the given position code.
     * @see NonTerminalProgramElement#getChildPositionCode(ProgramElement)
     * @deprecated
     */
    @Deprecated
    int getIndexOfChild(int positionCode);

    /**
     * Extracts the role of a child from its position code. This information is required internally
     * for proper undo of transformations.
     *
     * @param positionCode the position code.
     * @return the role code of the given position code.
     * @see NonTerminalProgramElement#getChildPositionCode(ProgramElement)
     */
    int getRoleOfChild(int positionCode);

    /**
     * Ensures that each child has "this" as syntactical parent. Any class should define this method
     * for added attributes, and delegate to super.makeParentRoleValid() to ensure that inherited
     * attributes are made valid as well (e.g. comments from {@link SourceElement}). Any constructor
     * of a concrete class should call this method before returning if it shall leave a consistent
     * state.
     */
    void makeParentRoleValid();

    /**
     * Calls {@link #makeParentRoleValid}for each non terminal in the subtree with the current
     * element as root. If this instanceof TerminalProgramElement, nothing happens.
     */
    void makeAllParentRolesValid();

    /**
     * Calls {@link #validate}for each for the entire subtree with the current element as root.
     *
     * @since 0.80
     */
    void validateAll() throws ModelException;

    /**
     * Replace a single non-null child in the current node. The child to replace is matched by
     * identity and hence must be known exactly. The replacement element can be null - in that case,
     * the child is effectively removed. The parent role of the new child is validated, while the
     * parent link of the replaced child is left untouched.
     *
     * @param p the old child.
     * @param q the new child.
     * @return true if a replacement has occured, false otherwise.
     * @throws ClassCastException if the new child cannot take over the role of the old one.
     */
    boolean replaceChild(ProgramElement p, ProgramElement q);

    /**
     * Get the compilation unit that contains this program element.
     *
     * @return the compilation unit
     */
    default CompilationUnit compilationUnit() {
        NonTerminalProgramElement parent = getASTParent();
        if (parent != null) {
            return parent.compilationUnit();
        } else {
            return null;
        }
    }
}
