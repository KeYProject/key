/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.convenience;

import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;

/**
 * A listener for AST traversal events signaled by ASTIterators.
 *
 * @author RN
 */
public interface ASTIteratorListener {

    /**
     * Return value for ASTListener methods, that signals that no child node should be entered.
     */
    int ENTER_NONE = ASTIterator.ENTER_NONE;

    /**
     * Return value for ASTListener methods, that signals that only some children nodes should be
     * entered - each child will be queried separately.
     */
    int ENTER_SOME = ASTIterator.ENTER_SOME;

    /**
     * Return value for ASTListener methods, that signals that all children should be entered
     * without further questions.
     */
    int ENTER_ALL = ASTIterator.ENTER_ALL;

    /**
     * This method is called whenever an AST node is entered.
     *
     * @param it the ASTIterator that called this method.
     * @param node the node that is currently entered.
     */
    void enteringNode(ASTIterator it, ProgramElement node);

    /**
     * This method is called just before an AST node is left.
     *
     * @param it the ASTIterator that called this method.
     * @param node the node that is about to be left.
     */
    void leavingNode(ASTIterator it, ProgramElement node);

    /**
     * Called to determine whether or not children nodes should be visited.
     *
     * @param it the ASTIterator that called this method.
     * @param thisNode the current node.
     * @return either ENTER_NONE, ENTER_SOME or ENTER_ALL.
     */
    int enterChildren(ASTIterator it, NonTerminalProgramElement thisNode);

    /**
     * Determines whether or not a given child node should be visited.
     *
     * @param it the ASTIterator that called this method.
     * @param thisNode the current node.
     * @param childNode the child node that might be visited next.
     * @return <tt>true</tt> if the iterator should proceed to the given child node.
     */
    boolean enterChildNode(ASTIterator it, NonTerminalProgramElement thisNode,
            ProgramElement childNode);

    /**
     * Called immediately after the iterator returned from the child node.
     *
     * @param it the ASTIterator that called this method.
     * @param thisNode the current node.
     * @param childNode the child node that has just been visited.
     */
    void returnedFromChildNode(ASTIterator it, NonTerminalProgramElement thisNode,
            ProgramElement childNode);

}
