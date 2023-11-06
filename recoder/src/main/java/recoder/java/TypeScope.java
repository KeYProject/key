/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java;

import java.util.List;

import recoder.abstraction.ClassType;

/**
 * The property of a non terminal program element to define a scope for types.
 */

public interface TypeScope extends ScopeDefiningElement {

    List<? extends ClassType> getTypesInScope();

    ClassType getTypeInScope(String name);

    void addTypeToScope(ClassType type, String name);

    void removeTypeFromScope(String name);
}
