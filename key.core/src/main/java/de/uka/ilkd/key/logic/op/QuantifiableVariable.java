/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;


import org.key_project.util.EqualsModProofIrrelevancy;

/**
 * This interface represents the variables that can be bound (by quantifiers or other binding
 * operators).
 */
public interface QuantifiableVariable extends ParsableVariable, EqualsModProofIrrelevancy {
}
