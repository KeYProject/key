package de.uka.ilkd.key.lang.common.walker;

import de.uka.ilkd.key.lang.common.program.ArrayOfIProgramElement;
import de.uka.ilkd.key.lang.common.program.INonTerminalProgramElement;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.util.ExtList;
import de.uka.ilkd.key.util.SimpleStackOfExtList;

/**
 * A walker that maintains a stack of lists of element's children being
 * currently traversed (in depth left-first order). These lists can be marked as
 * modified if they contain modified copies of the children. When leaving AST
 * element the list at the top of the stack is popped and is treated as the new
 * list of children. If the list has been modified a new copy of the element is
 * created with the new children, otherwise the unmodiifed element is used. A
 * variety of AST transformations can be implemented by overriding non-final
 * methods. Override non-final methods to modify the behavior.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseCreatingWalker extends BaseWalker {

        /**
         * Implementation of the stack of lists.
         */

        private static final Boolean CHANGED = new Boolean(true);

        private final SimpleStackOfExtList stack = new SimpleStackOfExtList();

        /**
         * Initializes the creating walker with an empty list at the bottom of the stack.
         */
        protected BaseCreatingWalker() {
                push();
        }

        /**
         * Pushes an empty list onto the stack.
         */
        protected final void push() {
                stack.push(new ExtList());
        }

        /**
         * Pops the top list off the stack.
         * 
         * @return
         */
        protected final ExtList pop() {
                ExtList list = stack.pop();
                if (!list.isEmpty() && list.getFirst() == CHANGED)
                        list.removeFirst();
                return list;
        }

        /**
         * Peeks at the top list of the stack.
         * 
         * @return
         */
        protected final ExtList peek() {
                return stack.peek();
        }

        /**
         * Adds a child to the top list of the stack.
         * 
         * @param pe
         */
        protected final void addChild(IProgramElement pe) {
                ExtList list = stack.peek();
                list.add(pe);
        }

        /**
         * Adds an array of childer to the top list of the stack.
         * 
         * @param pe
         */
        protected final void addChildren(ArrayOfIProgramElement arr) {
                for (int i = 0, sz = arr.size(); i < sz; i++) {
                        addChild(arr.getIProgramElement(i));
                }
        }

        /**
         * Marks the current list at the top of the stack as modified.
         */
        protected final void markChanged() {
                ExtList list = stack.peek();
                if (list.isEmpty() || list.getFirst() != CHANGED) {
                        list.addFirst(CHANGED);
                }
        }

        /**
         * Tells if the list currently at the top of the stack was marked as
         * modified.
         * 
         * @return
         */
        protected final boolean wasChanged() {
                ExtList list = stack.peek();
                return (!list.isEmpty() && list.getFirst() == CHANGED);
        }

        /**
         * Walks the element. Pushes an empty list onto the stack to be
         * populated with possibly modified element's children. In the end
         * {@link doAction}$ is called that must pop the list of children and
         * add the element or its modified copy to the list at the top of the
         * stack, which will be treated as the list of element's parent's
         * children in turn.
         * 
         * @param pe
         */
        protected void walk(IProgramElement pe) {
                push();
                super.walk(pe);
        }

        /**
         * If the children of the element have been modified, pops them off the
         * stack and adds to the list at the top of the stack a copy of the
         * element containing the new children. Oherwise calls
         * {@link doDefaultAction}.
         * 
         * @param pe
         */
        protected void doAction(IProgramElement pe) {
                if (wasChanged()) {
                        addChild(copy(pe, pop()));
                        markChanged();
                } else {
                        doDefaultAction(pe);
                }
        }

        /**
         * Pops the element's children off the stack and adds unmodified element
         * to the list at the top of the stack.
         * 
         * @param node
         */
        protected void doDefaultAction(IProgramElement pe) {
                pop();
                addChild(pe);
        }

        /**
         * Makes a copy of a non-terminal program element containing the new
         * children, or returns the program element unmodified if this is not a
         * non-terminal program element.
         * 
         * @param original
         * @param newChildren
         * @return
         */
        protected IProgramElement copy(IProgramElement original,
                        ExtList newChildren) {
                if (original instanceof INonTerminalProgramElement)
                        return ((INonTerminalProgramElement) original)
                                        .copy(newChildren);
                else
                        return original;
        }
}
