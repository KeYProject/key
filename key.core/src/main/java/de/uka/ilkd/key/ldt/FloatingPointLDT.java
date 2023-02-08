/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.logic.op.Function;

public interface FloatingPointLDT {

    public Function getLessThan();

    public Function getGreaterThan();

    public Function getLessOrEquals();

    public Function getGreaterOrEquals();

    public Function getEquals();

    public Function getJavaUnaryMinus();

    public Function getJavaAdd();

    public Function getJavaSub();

    public Function getJavaMul();

    public Function getJavaDiv();

    public Function getJavaMod();

    public Function getJavaMin();

    public Function getJavaMax();

    public Function getIsNormal();

    public Function getIsSubnormal();

    public Function getIsNaN();

    public Function getIsZero();

    public Function getIsNice();

    public Function getIsInfinite();

    public Function getIsPositive();

    public Function getIsNegative();

    public Function getAdd();

    public Function getSub();

    public Function getMul();

    public Function getDiv();

    public Function getAbs();
}
