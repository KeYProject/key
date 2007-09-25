package de.uka.ilkd.key.lang.common.program;

import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.util.ExtList;

/**
 * Represents a non-terminal program element.
 * 
 * @author oleg.myrk@gmail.com
 */
public interface INonTerminalProgramElement extends IProgramElement,
                NonTerminalProgramElement {
        /**
         * Returns the number of children of this node.
         * 
         * @return an int giving the number of children of this node
         */
        int getChildCount();

        /**
         * Returns the child at the specified index in this node's "virtual"
         * child array.
         * 
         * @param index
         *                an index into this node's "virtual" child array
         * @return the program element at the given position
         * @exception ArrayIndexOutOfBoundsException
         *                    if <tt>index</tt> is out of bounds
         */
        IProgramElement getProgramElementAt(int index);
        
        /**
         * Makes a copy of this program element with new virtual children.
         * @param children
         * @return
         */
        IProgramElement copy(ExtList children);
}
