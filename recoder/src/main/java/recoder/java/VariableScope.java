// This file is part of the RECODER library and protected by the LGPL.

package recoder.java;

import recoder.java.declaration.VariableSpecification;

import java.util.List;

/**
 * The property of a non terminal program element to define a scope for variables.
 */

public interface VariableScope extends ScopeDefiningElement {

    List<? extends VariableSpecification> getVariablesInScope();

    VariableSpecification getVariableInScope(String name);

    void addVariableToScope(VariableSpecification var);

    void removeVariableFromScope(String name);
}
