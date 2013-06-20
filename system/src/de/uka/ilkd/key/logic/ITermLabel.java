// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic;

/**
 * The interface for term labels. Term labels are annotations that can be attached
 * to {@link Term}s and carry additional information. They must not be soundness relevant.
 */
public interface ITermLabel extends Named {
    /**
     * A term label may have structure, i.e., parameterized
     * @param i the i-th parameter (from 0 to max nr of parameters)
     * @return the selected parameter
     * @throw an {@link IndexOutOfBoundsException} if the given parameter number is negative or greater-or-equal the number of parameters returned by {@link #getChildCount()}
     */
    public abstract Object getChild(int i);

    /**
     * number of parameters (non-negative number)
     * @return the number of parameters
     */
    public abstract int getChildCount();
}