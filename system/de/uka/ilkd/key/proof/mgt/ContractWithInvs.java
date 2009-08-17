// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.OperationContract;


public class ContractWithInvs {
    
    public final OperationContract contract;
    public final ImmutableSet<ClassInvariant> assumedInvs;
    public final ImmutableSet<ClassInvariant> ensuredInvs;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    public ContractWithInvs(OperationContract contract, 
                            ImmutableSet<ClassInvariant> assumedInvs,
                            ImmutableSet<ClassInvariant> ensuredInvs) {
        assert contract != null;
        assert assumedInvs != null;
        assert ensuredInvs != null;
        this.contract    = contract;
        this.assumedInvs = assumedInvs;
        this.ensuredInvs = ensuredInvs;
    }
    
    
    /**
     * Creates a ContractWithInvs from a string originating from 
     * ContractWithInvs.toString().
     */
    public ContractWithInvs(String s, Services services) {
        String[] split = s.split(";", 3);        
        assert split.length == 3;
        String contractName      = split[0];
        String[] assumedInvNames = split[1].split(",");
        String[] ensuredInvNames = split[2].split(",");
        SpecificationRepository specRepos 
            = services.getSpecificationRepository();
        
        contract = specRepos.getOperationContractByName(contractName);
        assert contract != null;
        
        ImmutableSet<ClassInvariant> tempAssumedInvs 
            = DefaultImmutableSet.<ClassInvariant>nil();
        for(int i = assumedInvNames.length - 1; i >=0; i--) {
            if(!assumedInvNames[i].equals("")) {
                ClassInvariant inv 
                    = specRepos.getClassInvariantByName(assumedInvNames[i]);
                assert inv != null;
                tempAssumedInvs = tempAssumedInvs.add(inv);
            }
        }
        assumedInvs = tempAssumedInvs;
        
        ImmutableSet<ClassInvariant> tempEnsuredInvs 
            = DefaultImmutableSet.<ClassInvariant>nil();
        for(int i = ensuredInvNames.length - 1; i >= 0; i--) {
            if(!ensuredInvNames[i].equals("")) {
                ClassInvariant inv 
                    = specRepos.getClassInvariantByName(ensuredInvNames[i]);
                assert inv != null;
                tempEnsuredInvs = tempEnsuredInvs.add(inv);
            }
        }
        ensuredInvs = tempEnsuredInvs;
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    public String getHTMLText(Services services) {
        StringBuffer assumedSB = new StringBuffer();
        for(ClassInvariant inv : assumedInvs) {
            assumedSB.append("<br>" + inv.getHTMLText(services)
                                         .replaceAll("</?html>", ""));
        }
        
        StringBuffer ensuredSB = new StringBuffer();
        for(ClassInvariant inv : ensuredInvs) {
            ensuredSB.append("<br>" + inv.getHTMLText(services)
                                         .replaceAll("</?html>", ""));
        }
        
        return "<html>"
               + contract.getHTMLText(services).replaceAll("</?html>", "")
               + (assumedInvs.size() > 0
                  ? "<br><u>Assumed invariants:</u>" + assumedSB.toString()
                  : "")
               + (ensuredInvs.size() > 0
                  ? "<br><u>Ensured invariants:</u>" + ensuredSB.toString()
                  : "")
               + "</html>";
    }
    
    
    
    public String toString() {
        StringBuffer assumedSB = new StringBuffer();
        for(ClassInvariant inv : assumedInvs) {
            assumedSB.append(inv.getName() + ",");
        }
        
        StringBuffer ensuredSB = new StringBuffer();
        for(ClassInvariant inv : ensuredInvs) {
            ensuredSB.append(inv.getName() + ",");
        }
        
        return contract.getName() + ";" 
               + assumedSB.toString() + ";" 
               + ensuredSB.toString();
    }
    
    
        
    public boolean equals(Object o) {
        if(!(o instanceof ContractWithInvs)) {
            return false;
        }
        ContractWithInvs cwi = (ContractWithInvs) o;
        return contract.equals(cwi.contract) 
               && assumedInvs.equals(cwi.assumedInvs)
               && ensuredInvs.equals(cwi.ensuredInvs);
    }
    
    
    public int hashCode() {
        return contract.hashCode() 
               + assumedInvs.hashCode() 
               + ensuredInvs.hashCode();
    }
}
