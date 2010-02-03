// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/**
 * Just to make tests.
 */


package de.uka.ilkd.key.casetool.together.scripts.probe.helloworldcall;

import com.togethersoft.openapi.ide.IdeContext;
import com.togethersoft.openapi.ide.message.IdeMessageManagerAccess;
import com.togethersoft.openapi.ide.message.IdeMessageType;
import com.togethersoft.openapi.ide.project.IdeProjectManagerAccess;

import de.uka.ilkd.key.casetool.together.keydebugclassloader.KeyScript;


public class HelloJava extends KeyScript  {

    

    /**
     * Activate the script (cmp. KeyScript)
     */ 
    public void run1(IdeContext context) {
        IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION, "HelloJava new script: started");
	printProjectName();
    }

    /**
     * Activate the script (cmp. KeyScript)
     */ 
    public void autorun1() { 
        IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION, "HelloJava new script: started");
    }


    public void printProjectName() {
	String result;
	StringBuffer fullPath;
	StringBuffer fileName;
	StringBuffer dirName;
	if(IdeProjectManagerAccess.getProjectManager().getActiveProject() == null){
	    // no open project
	    result = "No open Project";
	}else{
	    fileName = new StringBuffer(IdeProjectManagerAccess.getProjectManager().getActiveProject().getName());
	    fullPath = new StringBuffer(IdeProjectManagerAccess.getProjectManager().getActiveProject().getFileName());
	    dirName = new StringBuffer(IdeProjectManagerAccess.getProjectManager().getActiveProject().getFileName());
	    dirName.replace(dirName.length() - (fileName.length() +1), dirName.length(), "");
	    result = 
		"Full path: " + fullPath.toString() + "\n" +
		"Project name: " + fileName.toString() + "\n" +
		"Dir name: " + dirName.toString();
	}
	IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION, result);
    }

}
