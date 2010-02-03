// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.util.ExtList;

/**
 * represents something in logic that originates from a program like
 * queries, program variables and therefore has a KeYJavaType
 */
public interface ProgramInLogic {

    Expression convertToProgram(Term t, ExtList list);

}
