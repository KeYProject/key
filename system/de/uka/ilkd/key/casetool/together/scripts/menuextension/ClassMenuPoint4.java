// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


/** @author Kristofer Johannisson */ 


package de.uka.ilkd.key.casetool.together.scripts.menuextension;

import javax.swing.ProgressMonitor;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.casetool.together.TogetherGFInterface;
import de.uka.ilkd.key.casetool.together.TogetherModelClass;
import de.uka.ilkd.key.ocl.gf.CallbackClassInv;
import de.uka.ilkd.key.ocl.gf.Utils;

public class ClassMenuPoint4 extends ClassMenu {
    protected static Logger timelogger = Logger.getLogger("de.uka.ilkd.key.ocl.gf.Timer");
    protected static Logger logger = Logger.getLogger("key.ocl.gf");

    public String getMenuEntry(){
	return "Edit Invariant [GF]";
    }

    protected String runCore(TogetherModelClass modelClass) {
	if (timelogger.isDebugEnabled()) {
		timelogger.debug(System.currentTimeMillis() + "  ObMenuPoint6 runCore");
	}
	if (logger.isDebugEnabled()) {            
		logger.debug("Class: " + modelClass.getFullClassName());
	}
	pm = new ProgressMonitor(null, "Loading the GF editor for OCL",
			         "", 0, 9700);
	Utils.tickProgress(pm, 1, "Initializing TogetherGFInterface");
            
        CallbackClassInv cci = new CallbackClassInv(modelClass);
        String name = modelClass.getClassName();
        String pack = modelClass.getContainingPackage();
        String inv = modelClass.getMyInv();
        String abs = modelClass.getMyInvGFAbs();
        
        // aReprModelClass.setMyInvGFAbs("just testing...");
        
    //    return (new GFinterface()).editClassInvariant(aReprModelClass.getClassName(),
    //    	aReprModelClass.getMyInv());
    	return (new TogetherGFInterface()).editClassInvariant(name, pack, inv, cci, pm, abs);
    }
}
