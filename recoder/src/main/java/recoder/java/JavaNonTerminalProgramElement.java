/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java;

import recoder.ModelException;
import recoder.convenience.TreeWalker;

/**
 * Top level implementation of a Java {@link NonTerminalProgramElement}.
 *
 * @author AL
 */

public abstract class JavaNonTerminalProgramElement extends JavaProgramElement
        implements NonTerminalProgramElement {

    /**
     * Java program element.
     */

    public JavaNonTerminalProgramElement() {
        // nothing to do here
    }

    /**
     * Java program element.
     *
     * @param proto a java program element.
     */

    protected JavaNonTerminalProgramElement(JavaProgramElement proto) {
        super(proto);
    }

    /**
     * Defaults to do nothing.
     */

    public void makeParentRoleValid() {
        // nothing to do here
    }

    /**
     * Defaults to attempt a depth-first traversal using a {@link recoder.convenience.TreeWalker}.
     */

    public void makeAllParentRolesValid() {
        TreeWalker tw = new TreeWalker(this);
        while (tw.next(NonTerminalProgramElement.class)) {
            ((NonTerminalProgramElement) tw.getProgramElement()).makeParentRoleValid();
        }
    }

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
    public int getIndexOfChild(int positionCode) {
        return positionCode >> 4;
    }

    /**
     * Extracts the role of a child from its position code.
     *
     * @param positionCode the position code.
     * @return the role code of the given position code.
     * @see NonTerminalProgramElement#getChildPositionCode(ProgramElement)
     */
    public int getRoleOfChild(int positionCode) {
        return positionCode & 15;
    }

    /**
     * Returns the index of the given child, or <CODE>-1</CODE> if there is no such child. The child
     * is searched for by identity: <CODE>
     * getChildAt(getIndexOfChild(x)) == x</CODE>.
     *
     * @param child the exact child to look for.
     * @return the index of the given child, or <CODE>-1</CODE>.
     */
    public int getIndexOfChild(ProgramElement child) {
        int i;
        for (i = getChildCount() - 1; i >= 0 && (getChildAt(i) != child); i--) {
            /* logic is contained in loop control */
        }
        return i;
    }

    public void validateAll() throws ModelException {
        TreeWalker tw = new TreeWalker(this);
        while (tw.next()) {
            tw.getProgramElement().validate();
        }
    }
}
