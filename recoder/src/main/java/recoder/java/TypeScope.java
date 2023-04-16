// This file is part of the RECODER library and protected by the LGPL.

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
