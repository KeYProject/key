/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;


/**
 * Operators implementing this interface may stand for locations as well. This means e.g. occur as
 * top level operators on the left side of an assignment pair of an update.
 */
public interface UpdateableOperator extends SortedOperator, ParsableVariable {

}
