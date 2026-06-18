/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.rule;

import java.util.Set;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Node;

/**
 * The return value of a side proof.
 *
 * @param result a term representing the result (first formula of succedent)
 * @param conditions formulas of the antecedent
 * @param node the final node of the side proof
 */
public record ResultsAndCondition(JTerm result, Set<JTerm> conditions, Node node) {
}
