// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.parser.jml;

import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;

public interface ArithOpProvider{

    public Namespace getFunctions();
    
    public void setFunctions(Namespace functions);

    public Function getAdd(boolean l);

    public Function getSub(boolean l);

    public Function getMinus(boolean l);

    public Function getMul(boolean l);

    public Function getDiv(boolean l);

    public Function getMod(boolean l);

    public Function getOr(boolean l);

    public Function getAnd(boolean l);

    public Function getXor(boolean l);

    public Function getNeg(boolean l);

    public Function getShiftRight(boolean l);

    public Function getShiftLeft(boolean l);

    public Function getMin(boolean l);

    public Function getMax(boolean l);

    public Function getCastToByte();

    public Function getCastToShort();

    public Function getCastToInt();

    public Function getCastToLong();

    public Function getUnsignedShiftRight(boolean l);

}
