/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
