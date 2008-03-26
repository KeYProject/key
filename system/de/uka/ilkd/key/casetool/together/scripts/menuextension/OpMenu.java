// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

// All implementing classes should have a name of 
// "OpMenu" + ...  

package de.uka.ilkd.key.casetool.together.scripts.menuextension;

import com.togethersoft.openapi.ide.IdeContext;
import com.togethersoft.openapi.ide.window.IdeDialogType;
import com.togethersoft.openapi.ide.window.IdeWindowManager;
import com.togethersoft.openapi.rwi.*;

import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.casetool.together.TogetherModelMethod;
import de.uka.ilkd.key.proof.init.ProofInputException;

import javax.swing.ProgressMonitor;



public abstract class  OpMenu {


    protected ProgressMonitor pm;

    public abstract String getMenuEntry();

    public abstract String getSubMenuName();

    public void run(IdeWindowManager winMan, 
	    	    IdeContext context, 
	    	    RwiModel rwiModel, 
	    	    RwiDiagram rwiDiagram){
        RwiElement[] selectedRwiElements = context.getRwiElements();
	RwiElement selectedRwiElement = selectedRwiElements[0];
	RwiReference selectedRef = rwiDiagram.findReference(selectedRwiElement);
	// if a operation is selected it is always a member (so the cast
	// shouldn't be dangerous
	RwiMember selectedMember = ((RwiMemberReference) selectedRef).getMember();
	TogetherModelMethod modelMethod 
		= new TogetherModelMethod(selectedMember, rwiModel, rwiDiagram);

	String result = "";
	try {
	    result = runCore(modelMethod);	    
	} catch(Exception e) {
	    e.printStackTrace(System.out);
	    result = e.toString();
	}
        
	if (!result.equals("")){
            if (pm!=null) pm.close();
    	    winMan.showMessageDialog("Result", IdeDialogType.INFORMATION, result);
	}
    }

    protected abstract String runCore(TogetherModelMethod modelMethod) 
    		throws ProofInputException;
}
