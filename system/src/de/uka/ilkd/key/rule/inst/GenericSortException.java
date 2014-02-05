// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.rule.inst;

/** 
 * This exception thrown if there is no appropriate instantiation of
 * the generic sorts occurring within an "SVInstantiations"-object 
 */
import de.uka.ilkd.key.collection.ImmutableList;

/** 
 * This exception thrown if there is no appropriate instantiation of
 * the generic sorts occurring within an "SVInstantiations"-object 
 */
public class GenericSortException extends SortException {

    /**
     * 
     */
    private static final long serialVersionUID = 1372231759025588273L;

    private ImmutableList<GenericSortCondition> conditions;
    
    public GenericSortException(String description, ImmutableList<GenericSortCondition> pConditions) {
            super(description);
            this.conditions = pConditions;
    } 
    
    public GenericSortException(String description) {
	super(description);
    } 

    public void setConditions(ImmutableList<GenericSortCondition> pConditions) {
            this.conditions = pConditions;
    }
    
    public String getMessage() {
	return super.getMessage() + (conditions == null ? "" : conditions);
    }
}
