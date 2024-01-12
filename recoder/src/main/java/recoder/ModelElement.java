/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder;

/**
 * A semantic part of the software model. A model element is not necessarily connected to a piece of
 * syntax.
 *
 * @see recoder.java.SourceElement
 */
public interface ModelElement {

    /**
     * Check consistency and admissibility of a construct, e.g. cardinality of participants.
     *
     * @throws ModelException
     */
    void validate() throws ModelException;
}
