// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.reference;

import recoder.java.NonTerminalProgramElement;

/**
 * Element that contains a PackageReference.
 *
 * @author AL
 */

public interface PackageReferenceContainer extends NonTerminalProgramElement {

    /**
     * Get the package reference.
     *
     * @return the package reference.
     */
    PackageReference getPackageReference();
}
