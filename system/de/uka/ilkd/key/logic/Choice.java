// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;


public class Choice implements Named{

    private final Name name;
    private Namespace funcNS = new Namespace();
    private final String category;

    /** 
     * creates a choice object with name <category>:<choice>.
     */
    public Choice(String choice, String category){
	this(new Name(category+":"+choice), category);
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

    public Name name(){
	return name;
    }

    public String category(){
	return category;
    }

    public Namespace funcNS(){
	return funcNS;
    }

    public void setFuncNS(Namespace funcNS){
	this.funcNS = funcNS;
    }

    public boolean equals(Object o) {
	if (!(o instanceof Choice)) {
	    return false;
	}
	final Choice c = (Choice)o;
	return category == c.category && name.equals(c.name);
	    
    }

    public int hashCode() {
	return name.hashCode()*37 + 
	    (category == null ? 13 : category.hashCode()*1369);
    }

    public Choice copy(){
	Choice c; 
	if(category==null){
	    c = new Choice(name);
	}else{
	    c = new Choice(name, category);
	}
	c.setFuncNS(funcNS.copy());
	return c;
    }

    public String toString(){
	return name.toString();
    }

}
