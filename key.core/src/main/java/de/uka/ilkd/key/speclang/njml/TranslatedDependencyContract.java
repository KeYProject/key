/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;

/**
 * The information obtain from an JML accessible clause.
 *
 * @author Alexander Weigl
 * @version 1 (23.04.24)
 */
public record TranslatedDependencyContract(IObserverFunction observerFunction, Term rhs, Term mby) {
}
