/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.IObserverFunction;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * The information obtain from an JML accessible clause.
 *
 * @author Alexander Weigl
 * @version 1 (23.04.24)
 */
@NullMarked
public record TranslatedDependencyContract(IObserverFunction observerFunction, JTerm rhs,
        @Nullable JTerm mby) {
}
