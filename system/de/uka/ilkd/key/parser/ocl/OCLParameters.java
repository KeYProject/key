// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.parser.ocl;

import de.uka.ilkd.key.logic.op.IteratorOfLogicVariable;
import de.uka.ilkd.key.logic.op.ListOfLogicVariable;
import de.uka.ilkd.key.util.Debug;


class OCLParameters {
    private final ListOfLogicVariable declaredVars;
    private final ListOfOCLEntity entities;
            
    public OCLParameters(ListOfLogicVariable declaredVars,
                         ListOfOCLEntity entities) {
        Debug.assertTrue(declaredVars != null);
        Debug.assertTrue(entities != null);
        this.declaredVars = declaredVars;
        this.entities        = entities;
    }
    
    
    public ListOfOCLEntity getEntities() {
        return entities;
    }
        
    
    public ListOfLogicVariable getDeclaredVars() {
        return declaredVars;
    }
    
    
    public String toString() {
        String result = "(";
        
        IteratorOfLogicVariable it = declaredVars.iterator();
        while(it.hasNext()) {
            result += it.next() + ",";
        }
        if(!declaredVars.isEmpty()) {
            result = result.substring(0, result.length() - 1) + "|";
        }
        
        IteratorOfOCLEntity it2 = entities.iterator();
        while(it2.hasNext()) {
            result += it2.next() + ",";
        }
        if(!entities.isEmpty()) {
            result = result.substring(0, result.length() - 1);
        }
        
        return result + ")";
    }
}
