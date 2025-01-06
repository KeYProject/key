/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;


import de.uka.ilkd.key.util.pp.Layouter;

import org.key_project.logic.Named;
import org.key_project.logic.ParsableVariable;

/**
 * This interface represents the root of a schema variable hierarchy to be express termstructures
 * that match on logical terms. Schema variables are used in Taclets where they act as placeholders
 * for other TermSymbols. The TermSymbols a SchemaVariable is allowed to match is specified by their
 * type and sort.
 */
public interface SchemaVariable extends org.key_project.logic.op.sv.SchemaVariable, ParsableVariable, Named {
    /**
     * Creates a parseable string representation of the declaration of the schema variable.
     *
     * @param l the layouter to use
     */
    void layout(Layouter<?> l);
}
