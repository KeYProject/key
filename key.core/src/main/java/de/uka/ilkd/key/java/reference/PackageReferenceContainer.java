package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.java.NonTerminalProgramElement;

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
