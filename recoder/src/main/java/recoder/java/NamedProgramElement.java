/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
// This file is part of the RECODER library and protected by the LGPL.

package recoder.java;

import recoder.NamedModelElement;

/**
 * Named program element.
 *
 * @author <TT>AutoDoc</TT>
 */

public interface NamedProgramElement extends NamedModelElement, NonTerminalProgramElement {

    /**
     * Get identifier.
     *
     * @return the identifier.
     */
    Identifier getIdentifier();

    /**
     * Set identifier.
     *
     * @param id an identifier.
     */
    void setIdentifier(Identifier id);
}
