/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic.op;

import org.key_project.logic.sort.Sort;

/**
 * This interface represents the variables that can be bound (by quantifiers or other binding
 * operators).
 */
public interface QuantifiableVariable<S extends Sort> extends ParsableVariable<S> {
}
