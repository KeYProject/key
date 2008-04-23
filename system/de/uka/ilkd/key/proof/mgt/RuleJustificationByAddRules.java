// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.proof.mgt;


import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;


public class RuleJustificationByAddRules implements RuleJustification{

    private final Node node;
    private final boolean isAxiom;

    public RuleJustificationByAddRules(Node node, boolean isAxiom) {
        assert node != null;
	this.node = node;
        this.isAxiom = isAxiom;
    }
    
    public boolean isAxiomJustification() {
	return isAxiom;
    }

    public RuleApp motherTaclet() {
	return node.getAppliedRuleApp();
    }

    public String toString() {
        LogicPrinter tacPrinter = new LogicPrinter 
            (new ProgramPrinter(null),                       
             NotationInfo.createInstance(),   
             node.proof().getServices(),
             true);      
        tacPrinter.printTaclet((Taclet)(motherTaclet().rule()));
	return "added rule justification \nintroduced at node "
                + node.serialNr() + " by rule \n" + tacPrinter;
    }
}
