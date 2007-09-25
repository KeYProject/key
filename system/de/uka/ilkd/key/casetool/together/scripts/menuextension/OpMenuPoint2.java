// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
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

import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.casetool.together.TogetherGFInterface;
import de.uka.ilkd.key.casetool.together.TogetherModelMethod;
import de.uka.ilkd.key.ocl.gf.CallbackPrePost;
import de.uka.ilkd.key.ocl.gf.Utils;

public class OpMenuPoint2 extends OpMenu {
    protected static Logger timelogger = Logger.getLogger("de.uka.ilkd.key.ocl.gf.Timer");
    protected static Logger logger = Logger.getLogger("key.ocl.gf");

    public String getMenuEntry(){
	return "Edit Pre/Postcondition [GF]";
    }

    public String getSubMenuName(){
	return null;
    }

    protected String runCore(ModelMethod modelMethod){
	if (timelogger.isDebugEnabled()) {
		timelogger.debug(System.currentTimeMillis() + "  ObMenuPoint6 runCore");
	}
	if (logger.isDebugEnabled()) {            
		logger.debug("Class: " + modelMethod.getContainingClassName());
		logger.debug("Signature: " + modelMethod.getCallSignature());
	}
	pm = new ProgressMonitor(null, "Loading the GF editor for OCL",
			         "", 0, 9700);
	Utils.tickProgress(pm, 1, "Initializing TogetherGFInterface");

	TogetherGFInterface tgfi = new TogetherGFInterface();
	TogetherModelMethod trpmm;
	try {
		trpmm = (TogetherModelMethod)modelMethod;
	} catch (ClassCastException e){
                String s = "This shouldn't happen: " + e;
		System.err.println(s);
		e.printStackTrace();
		return s;
	}
        String abs = modelMethod.getMyGFAbs();
        return (tgfi.editPrePost(
        	trpmm.getContainingClassName(),
        	trpmm.getContainingPackage(),
        	trpmm.getCallSignatureQualified(),
        	trpmm.getMyPreCond(),
        	trpmm.getMyPostCond(),
        	new CallbackPrePost(modelMethod),
        	trpmm.isQuery(), pm, abs)); //TODO this may return not the same as UMLOCLBehaviouralFeature.isQuery
    }
}
