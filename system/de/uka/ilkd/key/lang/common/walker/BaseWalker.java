package de.uka.ilkd.key.lang.common.walker;

import de.uka.ilkd.key.lang.common.program.INonTerminalProgramElement;
import de.uka.ilkd.key.lang.common.program.IProgramElement;

/**
 * Walks through an AST in depth-left-first-order. Implementing method
 * {@link BaseWalker#doAction} specifies the behaviour at the elements of the
 * AST. The walking behaviour can be changed by overriding method
 * {@link BaseWalker#walk}.
 */
public abstract class BaseWalker {
        /**
         * The current visited level.
         */
        protected int depth = -1;

        /**
         * Walks through the AST, while keeping track of the current element.
         * 
         * @param node
         *                the program element the walker is at
         */
        protected void walk(IProgramElement node) {
                if (node instanceof INonTerminalProgramElement) {
                        depth++;
                        INonTerminalProgramElement nonTerminalNode = (INonTerminalProgramElement) node;
                        for (int i = 0; i < nonTerminalNode.getChildCount(); i++) {
                                if (nonTerminalNode.getChildAt(i) != null) {
                                        walk(nonTerminalNode
                                                        .getProgramElementAt(i));
                                }
                        }
                        depth--;
                }
                doAction(node);
        }

        /**
         * The action that is performed just before leaving the node the last
         * time.
         */
        protected abstract void doAction(IProgramElement node);
}
