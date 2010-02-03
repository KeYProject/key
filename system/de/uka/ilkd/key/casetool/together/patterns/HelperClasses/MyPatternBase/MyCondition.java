// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.casetool.together.patterns.HelperClasses.MyPatternBase;

public class MyCondition implements com.togethersoft.openapi.ide.inspector.Condition{
    boolean flag=true;
    
    public void setFlag(boolean flag){
	this.flag=flag;
    }

    public boolean execute(com.togethersoft.openapi.ide.IdeContext context){
	//System.out.println("execute aufgerufen");
	return flag;
    }
}
