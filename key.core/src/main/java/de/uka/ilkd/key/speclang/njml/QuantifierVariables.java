/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.LogicVariable;

import org.key_project.util.collection.ImmutableList;

/**
 * @author Alexander Weigl
 * @version 1 (03.02.24)
 */
public record QuantifierVariables(KeYJavaType first, ImmutableList<LogicVariable> second) {
}
