// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

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
