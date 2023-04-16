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
