// This file is part of the RECODER library and protected by the LGPL.

package recoder.convenience;

import recoder.java.ProgramElement;

/**
 * An iterator for program elements.
 *
 * @since 0.71
 */
public interface ProgramElementWalker {

    /**
     * Proceeds to the next element, if available. Returns <CODE>true</CODE>, if there is one,
     * <CODE>false</CODE> otherwise.
     *
     * @return <CODE>true</CODE> if the iterator points to an object.
     */
    boolean next();

    /**
     * Returns the current ProgramElement of the iteration, or <CODE>null
     * </CODE> if {@link #next}has not yet been called or has returned <CODE>
     * false</CODE>.
     *
     * @return the current ProgramElement, or <CODE>null</CODE>.
     */
    ProgramElement getProgramElement();
}
