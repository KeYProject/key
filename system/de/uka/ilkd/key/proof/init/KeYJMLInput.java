// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design 
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.init;

import java.io.File;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.CompilationUnit;
import de.uka.ilkd.key.java.ConvertException;
import de.uka.ilkd.key.util.ProgressMonitor;


/**
 * sub-class of JavaInputWithJMLSpecBrowser which is used to parse just a
 * single JML-enriched java source file.
 * @deprecated
 */
public class KeYJMLInput extends JavaInputWithJMLSpecBrowser {

    public KeYJMLInput(String name, File file, boolean allIntMode, 
            ProgressMonitor monitor){
	super(name, file, allIntMode, monitor);	
    }

    public ProofSettings getPreferences() {
        settings = ProofSettings.DEFAULT_SETTINGS;
        return settings;
    }
    
    public String readJavaPath() throws ProofInputException {
	assert path != null;
	if(path.getParentFile() != null) {
	    return path.getParentFile().getAbsolutePath();
	} else {
	    return "./";
	}
    }
    
    
    public void readJML(CompilationUnit[] compUnits) throws ProofInputException {
        try {
            parseJMLSpecs(getTypesWithJMLSpecs(compUnits));
            //      initConfig.getServices().getImplementation2SpecMap().setProgVarNS(
            //          initConfig.progVarNS());
        } catch (ConvertException ce) {
            throw new ProofInputException(ce);
        }
    }

    /*
    public String readModel() throws ProofInputException{
        try {
            parseJMLSpecs(getTypesWithJMLSpecs(
                              getKeYJavaASTConverter().
                              readCompilationUnitsAsFiles(
                                  new String[]{path.getPath()})));
            //      initConfig.getServices().getImplementation2SpecMap().setProgVarNS(
            //          initConfig.progVarNS());
        } catch (ConvertException ce) {
            throw new ProofInputException(ce);
        }
        return null;
    }*/  
}
