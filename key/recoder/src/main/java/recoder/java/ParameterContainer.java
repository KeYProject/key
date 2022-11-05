// This file is part of the RECODER library and protected by the LGPL.

package recoder.java;

import recoder.java.declaration.ParameterDeclaration;

/**
 * Describes program elements that contain {@link recoder.java.declaration.ParameterDeclaration}s.
 *
 * @author AL
 */

public interface ParameterContainer extends StatementContainer {

    /**
     * Get the number of parameters in this container.
     *
     * @return the number of parameters.
     */
    int getParameterDeclarationCount();

    /*
     * Return the parameter declaration at the specified index in this node's "virtual" parameter
     * declaration array. @param index an index for a parameter declaration. @return the parameter
     * declaration with the given index. @exception ArrayIndexOutOfBoundsException if <tt> index
     * </tt> is out of bounds.
     */
    ParameterDeclaration getParameterDeclarationAt(int index);
}
