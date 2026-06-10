/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.ldt;

import org.key_project.logic.op.Function;

public interface IIntLdt {
    Function getNumberSymbol();

    Function getAdd();

    Function getMul();

    Function getMod();

    Function getDiv();

    Function getLessOrEquals();

    Function getGreaterOrEquals();

    Function getNegativeNumberSign();

    Function getNumberLiteralFor(int i);

    Function getNumberTerminator();
}
