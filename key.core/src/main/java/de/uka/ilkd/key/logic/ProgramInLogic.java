// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;

/**
 * represents something in logic that originates from a program like
 * queries, program variables and therefore has a KeYJavaType
 */
public interface ProgramInLogic {

    Expression convertToProgram(Term t, ExtList list);

}