/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.reference;

/**
 * ReferencePrefix and -suffix that is admissible for outer type references.
 */

public interface TypeReferenceInfix extends ReferencePrefix, ReferenceSuffix, NameReference {

    /**
     * Set reference prefix.
     *
     * @param prefix a reference prefix.
     */
    void setReferencePrefix(ReferencePrefix prefix);
}
