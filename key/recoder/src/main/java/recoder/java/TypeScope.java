/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
// This file is part of the RECODER library and protected by the LGPL.

package recoder.java;

import recoder.abstraction.ClassType;

import java.util.List;

/**
 * The property of a non terminal program element to define a scope for types.
 */

public interface TypeScope extends ScopeDefiningElement {

    List<? extends ClassType> getTypesInScope();

    ClassType getTypeInScope(String name);

    void addTypeToScope(ClassType type, String name);

    void removeTypeFromScope(String name);
}
