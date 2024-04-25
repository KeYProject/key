/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.SourceElement;

/**
 * This class is used to walk a tree of {@link SourceElement}s. The tree is
 * traversed in depth-first order, and the walker can be used to visit the
 * children of a node, the siblings of a node and the parent of a node.
 * <p>
 * The walker is backed by a stack, which is used to store the path from the root to the current
 * node.
 *
 * @author Tobias Reinhold
 */
public class JavaASTTreeWalker implements TreeWalker {
    /**
     * The root of the tree that is being walked.
     */
    private final SourceElement root;

    /**
     * The node of the tree the walker is currently at.
     */
    private SourceElement currentNode;

    /**
     * The stack used to store the path from the root to the current node.
     */
    private final Stack stack;

    /**
     * Creates a new {@link JavaASTTreeWalker} with the given {@code root} as the root of the tree.
     */
    public JavaASTTreeWalker(SourceElement root) {
        this.root = root;
        currentNode = root;
        stack = new Stack();
    }

    @Override
    public SourceElement root() {
        return root;
    }

    @Override
    public SourceElement currentNode() {
        return currentNode;
    }

    @Override
    public SourceElement firstChild() {
        if (currentNode instanceof NonTerminalProgramElement ntpe && ntpe.getChildCount() > 0) {
            // The index of the next child of the stored node to be visited is 1, as the first child
            // at index 0 is visited.
            stack.push(new NonTerminalProgramElementChildIndexPair(ntpe, 1));
            currentNode = ntpe.getChildAt(0);
            return currentNode;
        }
        return null;
    }

    @Override
    public SourceElement lastChild() {
        if (currentNode instanceof NonTerminalProgramElement ntpe && ntpe.getChildCount() > 0) {
            // The index of the next child of the stored node to be visited is childCount, as the
            // last child at index childCount - 1 is visited.
            // This signals that no more children are left to be visited.
            stack.push(
                new NonTerminalProgramElementChildIndexPair(ntpe, ntpe.getChildCount()));
            currentNode = ntpe.getChildAt(ntpe.getChildCount() - 1);
            return currentNode;
        }
        return null;
    }

    @Override
    public SourceElement nextNode() {
        // TreeWalker is depth-first, so if the current node has children, the first child is taken
        SourceElement node = firstChild();
        if (node != null) {
            return node;
        }
        // As the current node has no children, the next sibling would be the next node
        node = nextSibling();
        if (node != null) {
            return node;
        }
        // As the current node has no children and no next sibling, we have to go up the tree and
        // find siblings of the ancestors
        while (!stack.empty()) {
            parentNode();
            node = nextSibling();
            if (node != null) {
                return node;
            }
        }
        // The current node is the last node in the tree
        return null;
    }

    @Override
    public SourceElement previousNode() {
        // If the current node is the root, there is no previous node
        if (currentNode == root) {
            return null;
        }
        // If the current node has no previous sibling, it is a first child, and we must therefore
        // go to the parent
        SourceElement node = previousSibling();
        if (node == null) {
            node = parentNode();
            return node;
        }
        // As the current node has a previous sibling, we must go down the tree through all last
        // children to find the real previous node
        while (true) {
            SourceElement lastChild = lastChild();
            if (lastChild != null) {
                node = lastChild;
            } else {
                return node;
            }
        }
    }

    @Override
    public SourceElement nextSibling() {
        if (currentNode != root && !stack.empty()) {
            final NonTerminalProgramElementChildIndexPair parent = stack.peek();
            final NonTerminalProgramElement parentNode = parent.getNonTerminalProgramElement();
            final int parentChildIndex = parent.getNextChildToVisitIndex();
            if (parentChildIndex < parentNode.getChildCount()) {
                // The index of the next child of the parent on the stack that should be visited is
                // increased by one
                parent.setNextChildToVisitIndex(parentChildIndex + 1);
                currentNode = parentNode.getChildAt(parentChildIndex);
                return currentNode;
            }
        }
        return null;
    }

    @Override
    public SourceElement previousSibling() {
        if (currentNode != root && !stack.empty()) {
            final NonTerminalProgramElementChildIndexPair parent = stack.peek();
            final NonTerminalProgramElement parentNode = parent.getNonTerminalProgramElement();
            final int parentChildIndex = parent.getNextChildToVisitIndex();
            // parentChildIndex > 1 means that the current node is not the first child of its parent
            // => it has a previous sibling
            if (parentChildIndex > 1) {
                // The index of the next child of the parent on the stack that should be visited is
                // decreased by one
                parent.setNextChildToVisitIndex(parentChildIndex - 1);
                currentNode = parentNode.getChildAt(parentChildIndex - 2);
                return currentNode;
            }
        }
        return null;
    }

    @Override
    public SourceElement parentNode() {
        if (stack.empty()) {
            return null;
        }
        final NonTerminalProgramElementChildIndexPair parent = stack.pop();
        currentNode = parent.getNonTerminalProgramElement();
        return currentNode;
    }


    // ----------------- internal classes for easier handling of the tree ----------------- //

    /**
     * A pair consisting of a {@link NonTerminalProgramElement} and how many children of it have
     * already been visited.
     */
    private static class NonTerminalProgramElementChildIndexPair {
        /**
         * The {@link NonTerminalProgramElement} of the pair.
         */
        final NonTerminalProgramElement nonTerminalProgramElement;

        /**
         * The index of the next child of {@code nonTerminalProgramElement} that should be visited.
         */
        int nextChildToVisitIndex;

        /**
         * Constructs a new pair with the given {@code nonTerminalProgramElement} and index of the
         * next child to be visited.
         *
         * @param nonTerminalProgramElement the {@link NonTerminalProgramElement} of the pair
         * @param nextChildToVisitIndex the index of the next child of
         *        {@code nonTerminalProgramElement} that
         *        should to be visited
         */
        NonTerminalProgramElementChildIndexPair(NonTerminalProgramElement nonTerminalProgramElement,
                int nextChildToVisitIndex) {
            this.nonTerminalProgramElement = nonTerminalProgramElement;
            this.nextChildToVisitIndex = nextChildToVisitIndex;
        }

        /**
         * Sets the index of the next child of {@code nonTerminalProgramElement} that should to be
         * visited.
         *
         * @param nextChildToVisitIndex the index of the next child of
         *        {@code nonTerminalProgramElement} that
         *        should to be visited
         */
        void setNextChildToVisitIndex(int nextChildToVisitIndex) {
            this.nextChildToVisitIndex = nextChildToVisitIndex;
        }

        /**
         * Returns the index of the next child of {@code nonTerminalProgramElement} that should to
         * be visited.
         *
         * @return the index of the next child of {@code nonTerminalProgramElement} that should to
         *         be visited
         */
        int getNextChildToVisitIndex() {
            return nextChildToVisitIndex;
        }

        /**
         * Returns the {@link NonTerminalProgramElement} of the pair.
         *
         * @return the {@link NonTerminalProgramElement} of the pair
         */
        NonTerminalProgramElement getNonTerminalProgramElement() {
            return nonTerminalProgramElement;
        }
    }

    /**
     * Class used to store pairs of {@link NonTerminalProgramElement}s and how many children of each
     * have been already visited.
     */
    private static class Stack {
        /**
         * The array that is backing the stack.
         */
        NonTerminalProgramElementChildIndexPair[] stack;

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
            stack = new NonTerminalProgramElementChildIndexPair[standardInitialCapacity];
        }

        /**
         * Pushes a new element onto the stack.
         *
         * @param element the element to be pushed onto the stack
         */
        void push(NonTerminalProgramElementChildIndexPair element) {
            if (count >= stack.length) {
                resizeStack();
            }
            stack[count++] = element;
        }

        /**
         * Removes and returns the topmost element of the stack or {@code null} if the stack is
         * empty.
         *
         * @return the topmost element of the stack or {@code null} if the stack is empty
         */
        NonTerminalProgramElementChildIndexPair pop() {
            if (count == 0) {
                return null;
            }
            return stack[--count];
        }

        /**
         * Returns the topmost element of the stack without removing it or {@code null} if the stack
         * is empty.
         *
         * @return the topmost element of the stack or {@code null} if the stack is empty
         */
        NonTerminalProgramElementChildIndexPair peek() {
            if (count == 0) {
                return null;
            }
            return stack[count - 1];
        }

        /**
         * Returns whether the stack is empty.
         *
         * @return {@code true} if the stack is empty, {@code false} otherwise
         */
        boolean empty() {
            return count == 0;
        }

        /**
         * Increases the capacity of the stack.
         * <p>
         * Currently, the stack size is simply doubled.
         */
        void resizeStack() {
            NonTerminalProgramElementChildIndexPair[] newStack =
                new NonTerminalProgramElementChildIndexPair[stack.length * 2];
            System.arraycopy(stack, 0, newStack, 0, count);
            stack = newStack;
        }
    }
}
