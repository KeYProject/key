/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import org.key_project.logic.op.Function;
import de.uka.ilkd.key.logic.op.JavaDLFunction;

public interface FloatingPointLDT {

    JavaDLFunction getLessThan();

    JavaDLFunction getGreaterThan();

    JavaDLFunction getLessOrEquals();

    JavaDLFunction getGreaterOrEquals();

    JavaDLFunction getEquals();

    JavaDLFunction getJavaUnaryMinus();

    JavaDLFunction getJavaAdd();

    JavaDLFunction getJavaSub();

    JavaDLFunction getJavaMul();

    JavaDLFunction getJavaDiv();

    JavaDLFunction getJavaMod();

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

    JavaDLFunction getAdd();

    JavaDLFunction getSub();

    JavaDLFunction getMul();

    JavaDLFunction getDiv();

    Function getAbs();
}
