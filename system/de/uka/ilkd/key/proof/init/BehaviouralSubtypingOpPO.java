// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.casetool.ModelClass;
import de.uka.ilkd.key.casetool.UMLModelClass;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.mgt.Contract;
import de.uka.ilkd.key.proof.mgt.Contractable;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.util.Debug;


/**
* The "BehaviouralSubtypingOp" proof obligation. 
*/
public class BehaviouralSubtypingOpPO extends AbstractPO {

    private ListOfProofOblInput pairPOs;
    
    
   
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
  
    public BehaviouralSubtypingOpPO(UMLModelClass subtype, 
                                    ModelClass supertype, 
                                    Map contractPairs) {
        super("BehaviouralSubtypingOp of " + subtype.getClassName() + " and " 
                                           + supertype.getClassName(),
              subtype);
        pairPOs = SLListOfProofOblInput.EMPTY_LIST;
        
        Iterator it = contractPairs.entrySet().iterator();
        while(it.hasNext()) {
            Map.Entry e = (Map.Entry)(it.next());
            OperationContract subContract   = (OperationContract)(e.getKey());
            OperationContract superContract = (OperationContract)(e.getValue());
            ProofOblInput pairPO 
                    = new BehaviouralSubtypingOpPairPO(subContract, 
                                                       superContract); 
            pairPOs = pairPOs.append(pairPO); 
        }        
        Debug.assertFalse(pairPOs.isEmpty());
    }
    
  
  
    //-------------------------------------------------------------------------
    //methods of ProofOblInput interface
    //-------------------------------------------------------------------------      
  
    public void readProblem(ModStrategy mod) throws ProofInputException {
        int numPOs = pairPOs.size() * 2;
        poTerms = new Term[numPOs];
        poNames = new String[numPOs];
        
        IteratorOfProofOblInput it = pairPOs.iterator();
        int i = 0;
        while(it.hasNext()) {
            BehaviouralSubtypingOpPairPO pairPO 
                = (BehaviouralSubtypingOpPairPO)(it.next());
            pairPO.readProblem(mod);
            poTerms[i]   = pairPO.getTerm1();
            poNames[i++] = pairPO.name() + " - Pre";
            poTerms[i]   = pairPO.getTerm2();
            poNames[i++] = pairPO.name() + " - Post";
        }
    }

    
    public void setInitConfig(InitConfig conf) {
        super.setInitConfig(conf);
        IteratorOfProofOblInput it = pairPOs.iterator();
        while(it.hasNext()) {
            it.next().setInitConfig(conf);
        }
    }


    public Contractable[] getObjectOfContract() {
        return new Contractable[0];
    }

  
    public boolean initContract(Contract ct) {
        return false;
    }
}
