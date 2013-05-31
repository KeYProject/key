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


package de.uka.ilkd.key.gui.smt;

import javax.swing.JMenuItem;

import de.uka.ilkd.key.smt.SolverTypeCollection;

public class SMTMenuItem extends JMenuItem {
    private static final long serialVersionUID = 1L;
    private SolverTypeCollection solverUnion;

    public SMTMenuItem(SolverTypeCollection solverUnion) {
	super();
	this.solverUnion = solverUnion;
	this.setText(solverUnion.toString());
    }
    
    public SolverTypeCollection getSolverUnion() {
	return solverUnion;
    }
    
    public String toString(){
	return solverUnion.toString();
    }
}
