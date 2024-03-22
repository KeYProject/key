/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.logic.op.IObserverFunction;

import org.key_project.logic.sort.Sort;

public record Limit(Sort first, IObserverFunction second) {
}
