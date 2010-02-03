// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.unittest.simplify.ast;

import de.uka.ilkd.key.util.*;

public class Conjunction extends Term{

    public Conjunction(ExtList subs){
	super("AND", subs);
    }

    public Equation[] getEquations(){
	return (Equation[]) subs.collect(Equation.class);
    }

    public Inequation[] getInequations(){
	return (Inequation[]) subs.collect(Inequation.class);
    }

    public Less[] getLess(){
	return (Less[]) subs.collect(Less.class);
    }

    public LessEq[] getLessEq(){
	return (LessEq[]) subs.collect(LessEq.class);
    }

    public void add(Term t){
	subs.add(t);
    }

    public void removeLast(){
	subs.removeLast();
    }
}
