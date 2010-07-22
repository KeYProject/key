// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init.proofobligation;


import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.OperationContract;


/**
 * The "EnsuresPost" proof obligation.
 */
public class EnsuresPostPO extends AbstractEnsuresPostPO {
    
    public EnsuresPostPO(InitConfig initConfig, 
                         String name,
                         OperationContract contract,
                         ImmutableSet<ClassInvariant> assumedInvs) {
        super(initConfig,
              name,
              contract,
              assumedInvs,
              true);
    }


    public EnsuresPostPO(InitConfig initConfig, OperationContract contract,
            ImmutableSet<ClassInvariant> assumedInvs) {
        this(initConfig,
             "EnsuresPost ("
                 + contract.getProgramMethod() + ", "
                 + contract.getDisplayName() + ")",
             contract,
             assumedInvs);
    }
        
    public boolean implies(ProofOblInput po) {
        if(!(po instanceof EnsuresPostPO)) {
            return false;
        }
        EnsuresPostPO epPO = (EnsuresPostPO) po;
        return specRepos.splitContract(epPO.contract)
                        .subset(specRepos.splitContract(contract))
               && assumedInvs.subset(epPO.assumedInvs);
    }


    public boolean equals(Object o) {
        if(!(o instanceof EnsuresPostPO)) {
            return false;
        }
        EnsuresPostPO po = (EnsuresPostPO) o;
        return super.equals(po)
               && contract.equals(po.contract);
    }


    public int hashCode() {
        return super.hashCode() + contract.hashCode();
    }
}
