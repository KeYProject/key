// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.together.patterns.HelperClasses.MyParser;
public class Entry{

    String oclScheme;
    String property;
    String name;
    String propertyName;
    
    public Entry(String a, String b, String c, String d){
	this.oclScheme=a;
	this.property=b;
	this.name=c;
	this.propertyName = d;
    }


    public boolean equals(Object o) {
	if (o instanceof Entry) {
	    Entry e = (Entry) o;
	    if ((this.property.equals(e.property)) && (this.name.equals(e.name)) && (this.propertyName.equals(e.propertyName)) &&(this.oclScheme.equals(e.oclScheme))) 
		return true;
	    else
		return false;
	}else 
	    return false;
    }

    public int hashCode() {
        int hash = 0;
        if (oclScheme != null) hash += oclScheme.hashCode();
        if (property != null) hash += property.hashCode();
        if (propertyName != null) hash += propertyName.hashCode();
        if (name != null) hash += name.hashCode();
        return hash;
    }
    
    public String getOclSchemeName(){
	return this.oclScheme;
    }

    public String getProperty(){
	return this.property;
    }


    public String getName(){
	return this.name;
    }

    public String getPropertyName(){
	return this.propertyName;
    }

    public String toString(){
	return(this.property +";  "+ this.name +";  "+ this.propertyName +"\n");
    }

    
}
 
