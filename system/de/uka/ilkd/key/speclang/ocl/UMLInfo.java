// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.speclang.ocl;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;


public class UMLInfo {
    private final Services services;
    private final ImmutableList<Association> allAssociations;
    
    
    public UMLInfo(Services services, ImmutableList<Association> allAssociations) {
        this.services        = services;
        this.allAssociations = allAssociations;
    }
    
    
    /**
     * Returns all associations with at least one end in the passed type 
     * or one of its supertypes.
     */
    public ImmutableList<Association> getAssociations(KeYJavaType kjt) {
        assert kjt != null;
        ImmutableList<Association> result = ImmutableSLList.<Association>nil();

        for (Association allAssociation : allAssociations) {
            Association assoc = allAssociation;

            for (AssociationEnd associationEnd : assoc.getEnds()) {
                AssociationEnd end = associationEnd;
                String endClassName = end.getModelClass().getFullClassName();
                KeYJavaType endKjt
                        = services.getJavaInfo()
                        .getKeYJavaTypeByClassName(endClassName);

                if (services.getJavaInfo().isSubtype(kjt, endKjt)) {
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
    public ImmutableList<Association> getAssociations(KeYJavaType kjt, 
                                             String qualifier) {
        ImmutableList<Association> result = ImmutableSLList.<Association>nil();
        
        //iterate over all associations for the desired class
        ImmutableList<Association> classAssocs = getAssociations(kjt);
        for (Association classAssoc : classAssocs) {
            Association assoc = classAssoc;

            ImmutableList<AssociationEnd> ends = assoc.getEnds();
            if (ends.size() != 2) {
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
            ImmutableList<AssociationEnd> targetEnds = ImmutableSLList.<AssociationEnd>nil();
            if (javaInfo.isSubtype(kjt, end1Kjt)) {
                targetEnds = targetEnds.prepend(ends.tail().head());
            }
            if (javaInfo.isSubtype(kjt, end2Kjt)) {
                targetEnds = targetEnds.prepend(ends.head());
            }
            assert !targetEnds.isEmpty();

            //check if one of those ends has the desired role name
            for (AssociationEnd targetEnd : targetEnds) {
                AssociationEnd end = targetEnd;
                if (end.getRoleName().toString().equals(qualifier)) {
                    result = result.prepend(assoc);
                    break;
                }
            }
        }
        
        return result;
    }
}
