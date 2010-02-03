// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.unittest.simplify.ast;

public class Function{

    public static Function PLUS = new Function("+");
    public static Function MINUS = new Function("-");
    public static Function MUL = new Function("*");

    protected String name;

    public Function(String name){
	this.name = name;
    }

    public String name(){
	return name;
    }
    
    public String toSimplify(){
	return name;
    }

}
