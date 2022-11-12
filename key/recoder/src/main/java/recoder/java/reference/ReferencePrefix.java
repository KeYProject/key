/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.reference;

import recoder.java.ProgramElement;

/**
 * Reference prefix.
 *
 * @author <TT>AutoDoc</TT>
 */

public interface ReferencePrefix extends ProgramElement {

    /**
     * @return the parent qualifier, or null if there is none.
     */
    ReferenceSuffix getReferenceSuffix();

    /**
     * Set reference suffix.
     *
     * @param path a reference suffix.
     */
    void setReferenceSuffix(ReferenceSuffix path);
}
