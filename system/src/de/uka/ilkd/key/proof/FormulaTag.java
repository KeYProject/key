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


package de.uka.ilkd.key.proof;

/**
 * Class whose instances represent tags to identify the formulas of sequents
 * persistently, i.e. a tag does not become invalid when a formula is modified
 * by a rule application. Tags are managed by the class FormulaTagManager for
 * each Node
 */
public final class FormulaTag {

    static int counter = 0;
    int i;

    FormulaTag() {
    	i = counter++;
    }

    public String toString () {
    	return "" + i;
    }

}