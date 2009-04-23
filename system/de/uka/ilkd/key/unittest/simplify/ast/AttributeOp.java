// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest.simplify.ast;

public class AttributeOp extends Function{

    protected String attr, className;

    public AttributeOp(String className, String attr){
	super("|."+className+"::"+attr+"|");
	this.className = className;
	this.attr = attr;
    }

    public AttributeOp(String s){
	super(s);
    }

    public String getClassName(){
	return className;
    }

    public String getAttribute(){
	return attr;
    }

}
