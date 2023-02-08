/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
// This file is part of the RECODER library and protected by the LGPL.

package recoder.java;

/**
 * The property of a non terminal program element to define a scope. Scopes should not be accessed
 * from outside the SourceInfo service.
 */

public interface ScopeDefiningElement extends NonTerminalProgramElement {

    /**
     * Check if the scope has been set up.
     */
    boolean isDefinedScope();

    /**
     * Sets the scope to be defined or undefined. If set to defined, the scope cache becomes
     * initialized. If set to undefined, the scope cache becomes erased.
     */
    void setDefinedScope(boolean defined);
}
