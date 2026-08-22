/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics.theory;

import java.util.List;

import de.uka.ilkd.key.logic.JTerm;

import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.collection.ImmutableSet;

/**
 * One clause of a quantified formula, as trigger selection reads it.
 *
 * The clause is one conjunct of the formula's matrix. Its literals are listed with leading
 * negations stripped and if-then-else terms expanded, so a consumer sees each atom once and in
 * positive form. The universal variables are those of the formula that occur free in the clause;
 * a trigger of the clause has to bind them.
 *
 * @param clause the clause as it stands in the matrix
 * @param universalVariables the formula's universal variables occurring free in the clause
 * @param literals the literals, negations stripped, if-then-else expanded
 */
public record ClauseAnalysis(JTerm clause,
        ImmutableSet<QuantifiableVariable> universalVariables,
        List<JTerm> literals) {
}
