// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//


package de.uka.ilkd.key.counterexample;

public class Clause {
    private String comment;
    private String antecedent;
    private String consequent;

    public Clause(){}
    public Clause(String ante, String cnsq){
        antecedent = ante;
        consequent = cnsq;
    }
    public Clause(String ante, String cnsq, String com){
		antecedent = ante;
        consequent = cnsq;
        comment = "% "+com+ "\n\n";
    }

    public String toString(){
		return comment + antecedent + "->" + consequent + ".\n";
    }

	public void setComment(String com){
        comment = "% "+com+ "\n\n";
    }

	public void setAntecedent(String ante){
		antecedent = ante;
    }

	public void setConsequent(String cnsq){
		consequent = cnsq;
    }

    public String getClause(){
		return antecedent + "->" + consequent + ".\n";
    }
}
