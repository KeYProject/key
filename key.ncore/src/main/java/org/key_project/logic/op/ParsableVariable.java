/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic.op;


import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

/**
 * This interface represents the variables that can be recognized by one of the parsers.
 */
public interface ParsableVariable<S extends Sort<S>, T extends Term> extends SortedOperator<S, T> {
}
