/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.logic.op.JFunction;

import org.key_project.logic.op.Function;

public interface FloatingPointLDT {

    JFunction getLessThan();

    JFunction getGreaterThan();

    JFunction getLessOrEquals();

    JFunction getGreaterOrEquals();

    JFunction getEquals();

    JFunction getJavaUnaryMinus();

    JFunction getJavaAdd();

    JFunction getJavaSub();

    JFunction getJavaMul();

    JFunction getJavaDiv();

    JFunction getJavaMod();

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

    JFunction getAdd();

    JFunction getSub();

    JFunction getMul();

    JFunction getDiv();

    Function getAbs();
}
