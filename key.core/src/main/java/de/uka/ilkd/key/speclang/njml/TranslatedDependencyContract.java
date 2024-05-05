/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;

/**
 * Translated accessible clauses covering the {@link #observer} function (left-hand side),
 * the right-hand side {@link #rhs} as a term and the measures-by clause {@link #measuredBy}.
 *
 * @param observer   operator of the left-hand side
 * @param rhs        right-hand side
 * @param measuredBy decreasing term for termination
 * @author Alexander Weigl
 * @version 1 (23.04.24)
 */
public record TranslatedDependencyContract(IObserverFunction observer, Term rhs, Term measuredBy) {
}
