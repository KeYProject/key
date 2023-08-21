/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.convenience;

import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;

/**
 * A "generic" iterator that traverses an AST and notifies a possibly registered
 * ASTIteratorListener.
 *
 * @author RN
 */
public class ASTIterator {

    /**
     * Return value for ASTListener methods, that signals that no child node should be entered.
     */
    public static final int ENTER_NONE = 0;

    /**
     * Return value for ASTListener methods, that signals that only some children nodes should be
     * entered - each child will be queried separately.
     */
    public static final int ENTER_SOME = 1;

    /**
     * Return value for ASTListener methods, that signals that all children should be entered
     * without further questions.
     */
    public static final int ENTER_ALL = 2;

    /**
     * The listener that is notified during AST traversal.
     */
    ASTIteratorListener listener = null;

    /**
     * Creates a new ASTIterator.
     */
    public ASTIterator() {
        super();
    }

    /**
     * Creates a new ASTIterator assigned to the given listener.
     *
     * @param l the iterator listener
     */
    public ASTIterator(ASTIteratorListener l) {
        setListener(l);
    }

    /**
     * Assigns a certain listener to the iterator.
     *
     * @param l the listener
     */
    public void setListener(ASTIteratorListener l) {
        listener = l;
    }

    /**
     * Performs a depth first search traversal through the given AST.
     *
     * @param pe the AST element to iterate through
     */
    public void iterate(ProgramElement pe) {
        if (listener != null) {
            recurse(pe);
        } else {
            simpleRecurse(pe);
        }
    }

    /**
     * Recurses through the given AST in depth first search order. This method calls the
     * ASTIteratorListener methods.
     *
     * @param pe the current program element.
     */
    protected void recurse(ProgramElement pe) {
        if (pe != null) {
            listener.enteringNode(this, pe);
            if (pe instanceof NonTerminalProgramElement) {
                NonTerminalProgramElement ntpe = (NonTerminalProgramElement) pe;
                int childCount;
                switch (listener.enterChildren(this, ntpe)) {
                case ASTIterator.ENTER_NONE:
                    break;
                case ASTIterator.ENTER_SOME:
                    childCount = ntpe.getChildCount();
                    for (int i = 0; i < childCount; i++) {
                        ProgramElement child = ntpe.getChildAt(i);
                        if (listener.enterChildNode(this, ntpe, child)) {
                            recurse(child);
                            listener.returnedFromChildNode(this, ntpe, child);
                        }
                    }
                    break;
                case ASTIterator.ENTER_ALL:
                    childCount = ntpe.getChildCount();
                    for (int i = 0; i < childCount; i++) {
                        ProgramElement child = ntpe.getChildAt(i);
                        recurse(child);
                    }
                }
            }
            listener.leavingNode(this, pe);
        }
    }

    /**
     * Recurses through the given AST in depth first search order. This method is only called if no
     * iterator listener has been assigned. The purpose of this method is to be specialized within
     * subclasses:
     *
     * <PRE>
     * <p>
     * protected void simpleRecurse(ProgramElement pe) {
     * super.simpleRecurse(pe); dosomething(pe); }
     *
     * </PRE>
     *
     * @param pe the current program element.
     */
    protected void simpleRecurse(ProgramElement pe) {
        if (pe instanceof NonTerminalProgramElement) {
            NonTerminalProgramElement ntpe = (NonTerminalProgramElement) pe;
            int childCount = ntpe.getChildCount();
            for (int i = 0; i < childCount; i++) {
                ProgramElement child = ntpe.getChildAt(i);
                simpleRecurse(child);
            }
        }
    }

}
