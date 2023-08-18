/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;

/**
 * walks through a java AST in depth-left-fist-order at default. Implementing method doAction
 * specifies its behaviour at the different Nodes. The depth-left-fist behaviour can be changed by
 * overwriting the method <code> walk(ProgramElement) </code>.
 */
public abstract class JavaASTWalker {

    /**
     * the root the walker starts
     */
    private final ProgramElement root;

    /**
     * the current visited level
     */
    private int depth = -1;

    /**
     * create the JavaASTWalker
     *
     * @param root the ProgramElement where to begin
     */
    public JavaASTWalker(ProgramElement root) {
        this.root = root;
    }

    /**
     * returns start point of the walker
     *
     * @return root of the AST to walk through
     */
    public ProgramElement root() {
        return root;
    }

    /**
     * starts the walker
     */
    public void start() {
        walk(root);
    }

    /**
     * returns the current visited level
     */
    public int depth() {
        return depth;
    }

    /**
     * walks through the AST. While keeping track of the current node
     *
     * @param node the JavaProgramElement the walker is at
     */
    protected void walk(ProgramElement node) {
        if (node instanceof NonTerminalProgramElement) {
            depth++;
            NonTerminalProgramElement nonTerminalNode = (NonTerminalProgramElement) node;
            for (int i = 0; i < nonTerminalNode.getChildCount(); i++) {
                if (nonTerminalNode.getChildAt(i) != null) {
                    walk(nonTerminalNode.getChildAt(i));
                }
            }
            depth--;
        }
        // Otherwise, the node is left, so perform the action
        doAction(node);
    }

    /**
     * the action that is performed just before leaving the node the last time
     */
    protected abstract void doAction(ProgramElement node);
}
