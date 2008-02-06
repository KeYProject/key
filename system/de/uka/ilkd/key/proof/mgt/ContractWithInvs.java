// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.IteratorOfClassInvariant;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SetAsListOfClassInvariant;
import de.uka.ilkd.key.speclang.SetOfClassInvariant;


public class ContractWithInvs {
    
    public final OperationContract contract;
    public final SetOfClassInvariant assumedInvs;
    public final SetOfClassInvariant ensuredInvs;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    public ContractWithInvs(OperationContract contract, 
                            SetOfClassInvariant assumedInvs,
                            SetOfClassInvariant ensuredInvs) {
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
        
        SetOfClassInvariant tempAssumedInvs 
            = SetAsListOfClassInvariant.EMPTY_SET;
        for(int i = 0; i < assumedInvNames.length; i++) {
            if(!assumedInvNames[i].equals("")) {
                ClassInvariant inv 
                    = specRepos.getClassInvariantByName(assumedInvNames[i]);
                assert inv != null;
                tempAssumedInvs = tempAssumedInvs.add(inv);
            }
        }
        assumedInvs = tempAssumedInvs;
        
        SetOfClassInvariant tempEnsuredInvs 
            = SetAsListOfClassInvariant.EMPTY_SET;
        for(int i = 0; i < ensuredInvNames.length; i++) {
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
        IteratorOfClassInvariant it = assumedInvs.iterator();
        while(it.hasNext()) {
            assumedSB.append("<br>" + it.next().getHTMLText(services)
                                               .replaceAll("</?html>", ""));
        }
        
        StringBuffer ensuredSB = new StringBuffer();
        it = ensuredInvs.iterator();
        while(it.hasNext()) {
            ensuredSB.append("<br>" + it.next().getHTMLText(services)
                                               .replaceAll("</?html>", ""));
        }
        
        return "<html>"
               + contract.getHTMLText(services).replaceAll("</?html>", "")
               + (assumedInvs.size() > 0
                  ? "<br><u>Assumed invariants:</u>" + assumedSB.toString()
                  : "")
               + (ensuredInvs.size() > 0
                  ? "<u>Ensured invariants:</u>" + ensuredSB.toString()
                  : "")
               + "</html>";
    }
    
    
    
    public String toString() {
        StringBuffer assumedSB = new StringBuffer();
        IteratorOfClassInvariant it = assumedInvs.iterator();
        while(it.hasNext()) {
            assumedSB.append(it.next().getName() + ",");
        }
        
        StringBuffer ensuredSB = new StringBuffer();
        it = ensuredInvs.iterator();
        while(it.hasNext()) {
            assumedSB.append(it.next().getName() + ",");
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
