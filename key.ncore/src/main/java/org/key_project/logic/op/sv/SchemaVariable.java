/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic.op.sv;

import org.key_project.logic.op.ParsableVariable;

/// This interface represents the root of a schema variable hierarchy to be express termstructures
/// that match on logical terms. Schema variables are used in Taclets where they act as placeholders
/// for other TermSymbols. The TermSymbols a SchemaVariable is allowed to match is specified by
/// their
/// type and sort.
public interface SchemaVariable extends ParsableVariable {
    /// @return true if the schemavariable has the strict modifier which forces the instantiation to
    /// have exactly the same sort as the schemavariable (or if the sv is of generic sort -
    /// the instantiation of the generic sort)
    boolean isStrict();

    boolean isVariable();

    boolean isTerm();

    boolean isFormula();

    boolean isSkolemTerm();
}
