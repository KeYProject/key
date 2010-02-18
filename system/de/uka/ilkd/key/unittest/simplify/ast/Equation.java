// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest.simplify.ast;

public class Equation extends CompFormula{

    public Equation(){
	super("EQ");
    }

    public Equation(Term left, Term right){
	super("EQ", left, right);
    }

}
