/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.speclang;

import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.util.collection.ImmutableList;

public record ProgramVariableCollection(ProgramVariable self, ImmutableList<ProgramVariable> params, ProgramVariable result) {
}
