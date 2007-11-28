// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.proof.mgt;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.util.Debug;

public class ComplexRuleJustificationBySpec implements ComplexRuleJustification {

    private Map contract2Just = new HashMap();
   
    public ComplexRuleJustificationBySpec() {}
    
    public void add(Contract ct, RuleJustificationBySpec just) {
        contract2Just.put(ct, just);
    }
    
    public RuleJustification getSpecificJustification(RuleApp app, Services services) {
        if (app instanceof MethodContractRuleApp) {
            return (RuleJustification)
               contract2Just.get(((MethodContractRuleApp)app).getMethodContract());            
        } else if (app instanceof BuiltInRuleApp){
            return (RuleJustification) contract2Just.get
                     (UseMethodContractRule.INSTANCE.selectExistingContract
                             (services, app.posInOccurrence(), 
                              AutomatedContractConfigurator.INSTANCE));
        } else {
            Debug.fail(); // should never be the case
            return null;
        }
    }

    public DepAnalysis dependsOn(Proof p) {
        // TODO Auto-generated method stub
        return null;
    }

    public boolean isAxiomJustification() {
        return false;
    }

    public List getProofList() {
        return new LinkedList();
    }

}
