/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.logic.op.Function;

public interface FloatingPointLDT {

    Function getLessThan();

    Function getGreaterThan();

    Function getLessOrEquals();

    Function getGreaterOrEquals();

    Function getEquals();

    Function getJavaUnaryMinus();

    Function getJavaAdd();

    Function getJavaSub();

    Function getJavaMul();

    Function getJavaDiv();

    Function getJavaMod();

    Function getJavaMin();

    Function getJavaMax();

    Function getIsNormal();

    Function getIsSubnormal();

    Function getIsNaN();

    Function getIsZero();

    Function getIsNice();

    Function getIsInfinite();

    Function getIsPositive();

    Function getIsNegative();

    Function getAdd();

    Function getSub();

    Function getMul();

    Function getDiv();

    Function getAbs();
}
