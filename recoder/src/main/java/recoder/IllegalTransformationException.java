/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder;

/**
 * An exception indicating that a transformation performed on the abstract syntax tree leaves the
 * internal datastructures in an inconsistent state. This transformation is a &quot;workaround&quot;
 * for some known bugs. Currently, the exception is thrown only for one reason: When exchanging an
 * Identifier which is contained in a PackageSpecification. A workaround is to exchange either the
 * containing PackageReference or the containing PackageSpecification.
 *
 * @author Tobias Gutzmann
 */
public class IllegalTransformationException extends RuntimeException {
    /**
     *
     */
    public IllegalTransformationException() {
        // standard constructor
    }

    /**
     * @param message
     */
    public IllegalTransformationException(String message) {
        super(message);
    }
}
