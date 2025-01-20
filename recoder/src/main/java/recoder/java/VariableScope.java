/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java;

import java.util.List;

import recoder.java.declaration.VariableSpecification;

/**
 * The property of a non terminal program element to define a scope for variables.
 */

public interface VariableScope extends ScopeDefiningElement {

    List<? extends VariableSpecification> getVariablesInScope();

    VariableSpecification getVariableInScope(String name);

    void addVariableToScope(VariableSpecification var);

    void removeVariableFromScope(String name);
}
