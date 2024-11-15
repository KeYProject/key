/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.fn;

import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.VariableDeclaration;
import org.key_project.rusty.ast.abstraction.KeYRustyType;

public interface FunctionParam extends RustyProgramElement, VariableDeclaration {
    KeYRustyType getKeYRustyType();
}
