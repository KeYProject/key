/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op.sv;


/**
 * This interface represents the root of a schema variable hierarchy to be express termstructures
 * that match on logical terms. Schema variables are used in Taclets where they act as placeholders
 * for other TermSymbols. The TermSymbols a SchemaVariable is allowed to match is specified by their
 * type and sort.
 */
public interface SchemaVariable extends org.key_project.logic.op.sv.SchemaVariable {
    @Override
    default boolean isFormula() { return false; }

    @Override
    default boolean isVariable() { return false; }

    @Override
    default boolean isTerm() { return false; }

    @Override
    default boolean isSkolemTerm() { return false; }
}
