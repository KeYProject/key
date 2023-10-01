/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
