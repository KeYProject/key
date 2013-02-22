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


package de.uka.ilkd.key.logic;


public class Choice implements Named {

    private final Name name;
    private final String category;

    /** 
     * creates a choice object with name <category>:<choice>.
     */
    public Choice(String choice, String category){
	this(new Name(category + ":" + choice), category);
    }
    

    public Choice(Name name, String category){
	this.name = name;
	// .intern() crucial for correct equals
	this.category = category.intern();       
    }

    
    public Choice(Name name){
	this.name = name;
	category  = null;
    }

    
    @Override
    public Name name(){
	return name;
    }

    public String category(){
	return category;
    }

    
    @Override
    public boolean equals(Object o) {
	if (!(o instanceof Choice)) {
	    return false;
	}
	final Choice c = (Choice)o;
	return category == c.category && name.equals(c.name);
	    
    }

    
    @Override
    public int hashCode() {
	return name.hashCode()*37 + 
	    (category == null ? 13 : category.hashCode()*1369);
    }


    @Override
    public String toString(){
	return name.toString();
    }
}
