// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//


package de.uka.ilkd.key.rule.export;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;



public class CategoryModelInfo implements Named, Comparable<CategoryModelInfo> {
    private Name name;
    private ListOfOptionModelInfo options = SLListOfOptionModelInfo.EMPTY_LIST;
    
    public CategoryModelInfo ( String category ) {
        name = new Name ( category );
    }
    
    public void addOption ( OptionModelInfo opt ) {
        if ( !options.contains(opt) ) {
            options = options.prepend ( opt );
        }
    }
    
    public void setOptions ( ListOfOptionModelInfo p_options ) {
        this.options = p_options;
    }
    
    public ListOfOptionModelInfo getOptions () {
        return options;
    }
    
    @Override
    public Name name () {
        return name;
    }
    
    @Override
    public String toString () {
        return name.toString ();
    }

    @Override
    public int compareTo ( CategoryModelInfo other ) {
        return name.compareTo ( other.name );
    }
    
    @Override
    public boolean equals(Object o) {
	if(!(o instanceof CategoryModelInfo)) {
	    return false;
	}
	CategoryModelInfo cmi = (CategoryModelInfo)o;
	return compareTo(cmi) == 0;
    }
    
    @Override
    public int hashCode() {
	return name.hashCode();
    }
}
