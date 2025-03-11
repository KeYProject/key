/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.abstraction;

/**
 * A program model element representing constructors. Constructors are modelled as subtypes of
 * methods and will return the enclosing type as return type.
 */
public interface Constructor extends Method {
}
