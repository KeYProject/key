//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.ocl.translation;

import de.uka.ilkd.key.logic.op.IteratorOfLogicVariable;
import de.uka.ilkd.key.logic.op.ListOfLogicVariable;
import de.uka.ilkd.key.speclang.translation.ListOfSLExpression;
import de.uka.ilkd.key.speclang.translation.SLListOfSLExpression;
import de.uka.ilkd.key.speclang.translation.SLParameters;
import de.uka.ilkd.key.util.Debug;


class OCLParameters extends SLParameters {
    private final ListOfLogicVariable declaredVars;
    private final ListOfOCLExpression entities;
            
    public OCLParameters(ListOfLogicVariable declaredVars,
                         ListOfOCLExpression entities) {
        super(convertToListOfSLExpression(entities));
        Debug.assertTrue(declaredVars != null);
        Debug.assertTrue(entities != null);
        this.declaredVars = declaredVars;
        this.entities        = entities;
    }
    
    
    private static ListOfSLExpression convertToListOfSLExpression(ListOfOCLExpression list) {
        ListOfSLExpression result = SLListOfSLExpression.EMPTY_LIST;
        
        IteratorOfOCLExpression it = list.iterator();
        
        while(it.hasNext()) {
            result = result.append(it.next());
        }
        
        return result;
    }


    public ListOfOCLExpression getEntities() {
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
        
        IteratorOfOCLExpression it2 = entities.iterator();
        while(it2.hasNext()) {
            result += it2.next() + ",";
        }
        if(!entities.isEmpty()) {
            result = result.substring(0, result.length() - 1);
        }
        
        return result + ")";
    }
}
