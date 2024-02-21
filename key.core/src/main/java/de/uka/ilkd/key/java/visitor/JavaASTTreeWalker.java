/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.SourceElement;

public class JavaASTTreeWalker implements TreeWalker {
    private SourceElement root;

    private SourceElement currentNode;

    @Override
    public SourceElement getRoot() {
        return root;
    }

    @Override
    public SourceElement getCurrentNode() {
        return currentNode;
    }

    @Override
    public SourceElement firstChild() {
        if (currentNode instanceof NonTerminalProgramElement ntpe && ntpe.getChildCount() > 0) {
            currentNode = ntpe.getChildAt(0);
            return currentNode;
        }
        return null;
    }

    @Override
    public SourceElement lastChild() {
        if (currentNode instanceof NonTerminalProgramElement ntpe && ntpe.getChildCount() > 0) {
            currentNode = ntpe.getChildAt(ntpe.getChildCount() - 1);
            return currentNode;
        }
        return null;
    }

    @Override
    public SourceElement nextNode() {
        return null;
    }

    @Override
    public SourceElement previousNode() {
        return null;
    }

    @Override
    public SourceElement nextSibling() {
        return null;
    }

    @Override
    public SourceElement previousSibling() {
        return null;
    }

    @Override
    public SourceElement parentNode() {
        return null;
    }

    private record SourceElementChildIndexPair(SourceElement sourceElement, int childIndex) {}

    /**
     * Class used to store pairs of {@link SourceElement}s and how many children of each have been
     * already visited.
     */
    private class Stack {
        /**
         * The array that is backing the stack.
         */
        SourceElementChildIndexPair[] stack;

        /**
         * The number of elements contained in the stack.
         * <p>
         * {@code count} therefore points to the next free spot available in the {@code stack}.
         */
        int count;

        /**
         * Constructs a new {@link Stack} with an initial capacity of 16 elements.
         */
        public Stack() {
            final int standardInitialCapacity = 16;
            stack = new SourceElementChildIndexPair[standardInitialCapacity];
        }

        /**
         * Pushes a new element onto the stack.
         *
         * @param element the element to be pushed onto the stack
         */
        void push(SourceElementChildIndexPair element) {
            if (count >= stack.length) {
                resizeStack();
            }
            stack[count++] = element;
            return;
        }

        /**
         * Removes and returns the topmost element of the stack.
         *
         * @return the topmost element of the stack
         */
        SourceElementChildIndexPair pop() {
            return stack[--count];
        }

        /**
         * Returns the number of elements currently contained in the stack.
         *
         * @return the number of elements currently contained in the stack
         */
        int size() {
            return count;
        }

        /**
         * Empties the stack.
         * <p>
         * {@code count} is simply set to 0.
         */
        void reset() {
            count = 0;
        }

        /**
         * Increases the capacity of the stack.
         * <p>
         * Currently, the stack size is simply doubled.
         */
        void resizeStack() {
            SourceElementChildIndexPair[] newStack =
                new SourceElementChildIndexPair[stack.length * 2];
            System.arraycopy(stack, 0, newStack, 0, count);
            stack = newStack;
        }
    }
}
