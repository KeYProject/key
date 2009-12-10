// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.speclang.OperationContract;


/**
* The "BehaviouralSubtypingOp" proof obligation.
*/
public class BehaviouralSubtypingOpPO extends AbstractPO {

    private ImmutableList<ProofOblInput> pairPOs;



    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    public BehaviouralSubtypingOpPO(InitConfig initConfig,
	    			    KeYJavaType subKJT,
                                    KeYJavaType superKJT,
                                    Map<OperationContract, OperationContract> contractPairs) {
        super(initConfig,
              "BehaviouralSubtypingOp of " + subKJT.getName() + " and "
                                           + superKJT.getName(),
              subKJT);
        pairPOs = ImmutableSLList.<ProofOblInput>nil();

        for (Object o : contractPairs.entrySet()) {
            Map.Entry<OperationContract, OperationContract> e = (Map.Entry<OperationContract, OperationContract>) o;
            OperationContract subContract = e.getKey();
            OperationContract superContract = e.getValue();
            ProofOblInput pairPO
                    = new BehaviouralSubtypingOpPairPO(initConfig,
                    subContract,
                    superContract);
            pairPOs = pairPOs.append(pairPO);
        }
        assert !pairPOs.isEmpty();
    }



    //-------------------------------------------------------------------------
    //methods of ProofOblInput interface
    //-------------------------------------------------------------------------

    public void readProblem(ModStrategy mod) throws ProofInputException {
        int numPOs = pairPOs.size() * 2;
        poTerms = new Term[numPOs];
        poNames = new String[numPOs];

        Iterator<ProofOblInput> it = pairPOs.iterator();
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
}
