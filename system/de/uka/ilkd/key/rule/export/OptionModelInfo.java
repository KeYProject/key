// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design 
//Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                      and Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License.
//See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.export;

import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Name;



public class OptionModelInfo extends AbstractTacletContainer implements
        Comparable<OptionModelInfo> {
    private final Choice choice;
    private CategoryModelInfo category;
    
    public OptionModelInfo ( Choice p_choice ) {
        choice = p_choice;
    }
    
    public Choice getChoice () {
        return choice;
    }
    
    @Override
    public Name name () {
        return choice.name();
    }

    @Override
    public int compareTo ( OptionModelInfo o ) {
        return name().compareTo(o.name());
    }

    /**
     * @return Returns the category.
     */
    public CategoryModelInfo getCategory () {
        return category;
    }
    
    /**
     * @param category The category to set.
     */
    public void setCategory ( CategoryModelInfo category ) {
        this.category = category;
    }
    
    @Override
    public boolean equals(Object o) {
	if(!(o instanceof OptionModelInfo)) {
	    return false;
	}
	OptionModelInfo omi = (OptionModelInfo)o;
	return compareTo(omi) == 0;
    }
    
    @Override
    public int hashCode() {
	return name().hashCode();
    }
}