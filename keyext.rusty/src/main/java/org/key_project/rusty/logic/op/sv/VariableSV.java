/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op.sv;

import org.key_project.logic.Name;
import org.key_project.logic.TerminalSyntaxElement;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;

import org.jspecify.annotations.NonNull;

public class VariableSV extends OperatorSV implements QuantifiableVariable, TerminalSyntaxElement {
    /**
     * Creates a new SchemaVariable that is used as placeholder for bound(quantified) variables.
     *
     * @param name the Name of the SchemaVariable
     * @param sort the Sort of the SchemaVariable and the matched type
     */
    VariableSV(Name name, Sort sort) {
        super(name, sort, true, false);
    }


    @Override
    public @NonNull String toString() {
        return toString("variable");
    }
}
