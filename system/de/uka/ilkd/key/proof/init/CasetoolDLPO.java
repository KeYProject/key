// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.speclang.ocl.ModelClass;


public class CasetoolDLPO extends KeYUserProblemFile {

    private ModelClass aClRepr;

    public CasetoolDLPO(ModelClass reprModelCl, java.io.File file) {
	super(file.getName(), file, null);
	this.aClRepr=reprModelCl;
    }

/*
    public String readModel() {
	if (initConfig==null) {
	    throw new IllegalStateException("KeYFile: InitConfig not set.");
	}	
	final String[] cus = aClRepr.getClassesInPackage();        	
        getKeYJavaASTConverter().readCompilationUnitsAsFiles(cus);
        return aClRepr.getRootDirectory();
    }
*/

}
