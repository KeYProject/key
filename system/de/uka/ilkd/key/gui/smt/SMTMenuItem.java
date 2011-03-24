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
