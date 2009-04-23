// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest.simplify.ast;


//a comparison operation between two terms.
public class CompFormula extends Term{

    public CompFormula(String op){
	super(op);
    }

    public CompFormula(String op, Term left, Term right){
	super(op);
	subs.add(left);
	subs.add(right);
    }

    public void setLeft(Term t){
	setSub(0, t);
    }

    public void setRight(Term t){
	setSub(1, t);
    }

}
