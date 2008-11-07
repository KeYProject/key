// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.casetool;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.speclang.ocl.translation.*;


public class UMLInfo {
    private final Services services;
    private final ListOfAssociation allAssociations;
    
    
    public UMLInfo(Services services, ListOfAssociation allAssociations) {
        this.services        = services;
        this.allAssociations = allAssociations;
    }
    
    
    /**
     * Returns all associations with at least one end in the passed type 
     * or one of its supertypes.
     */
    public ListOfAssociation getAssociations(KeYJavaType kjt) {
        assert kjt != null;
        ListOfAssociation result = SLListOfAssociation.EMPTY_LIST;
        
        IteratorOfAssociation it = allAssociations.iterator();
        while(it.hasNext()) {
            Association assoc = it.next();
            
            IteratorOfAssociationEnd it2 = assoc.getEnds().iterator();
            while(it2.hasNext()) {
                AssociationEnd end = it2.next();
                String endClassName = end.getModelClass().getFullClassName();
                KeYJavaType endKjt 
                	= services.getJavaInfo()
                	          .getKeYJavaTypeByClassName(endClassName);
                
                if(services.getJavaInfo().isSubtype(kjt, endKjt)) {
                    result = result.prepend(assoc);
                    break;
                }
            }
        }
        
        return result;
    }
    
    
    /**
     * Returns all binary associations with at least one end in the passed type,
     * and whose role name on the other side is the passed string.
     */
    public ListOfAssociation getAssociations(KeYJavaType kjt, 
                                             String qualifier) {
        ListOfAssociation result = SLListOfAssociation.EMPTY_LIST;
        
        //iterate over all associations for the desired class
        ListOfAssociation classAssocs = getAssociations(kjt);
        IteratorOfAssociation it = classAssocs.iterator();
        while(it.hasNext()) {
            Association assoc = it.next();
            
            ListOfAssociationEnd ends = assoc.getEnds();
            if(ends.size() != 2) {
                continue;
            }

            //identify possible "other side" ends
            JavaInfo javaInfo = services.getJavaInfo();
            String end1ClassName 
            	= ends.head().getModelClass().getFullClassName();
            String end2ClassName 
            	= ends.tail().head().getModelClass().getFullClassName();
            KeYJavaType end1Kjt = javaInfo.getTypeByClassName(end1ClassName);
            KeYJavaType end2Kjt = javaInfo.getTypeByClassName(end2ClassName);
            ListOfAssociationEnd targetEnds = SLListOfAssociationEnd.EMPTY_LIST;
            if(javaInfo.isSubtype(kjt, end1Kjt)) {
                targetEnds = targetEnds.prepend(ends.tail().head());
            }
            if(javaInfo.isSubtype(kjt, end2Kjt)) {
                targetEnds = targetEnds.prepend(ends.head());
            }
            assert !targetEnds.isEmpty();
            
            //check if one of those ends has the desired role name
            IteratorOfAssociationEnd it2 = targetEnds.iterator();
            while(it2.hasNext()) {
                AssociationEnd end = it2.next();                
                if(end.getRoleName().toString().equals(qualifier)) {
                    result = result.prepend(assoc);
                    break;
                }
            }
        }
        
        return result;
    }
}
