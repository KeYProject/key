// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.proof.init;

import java.io.File;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.JMLSpecBrowser;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.util.ProgressMonitor;

/**
 * This class extends the JavaInput by opening the JML Specification Browser
 * after loading the java source files and contained JML specifications.
 * @deprecated
 */
public class JavaInputWithJMLSpecBrowser extends JavaInput {

    private JMLProofOblInput jmlPO;   
    
    /**
     * @param name    name of the input, will be the name of the created environment
     * @param path    path of the java files
     * @param monitor ProgressMonitor for showing progress while loading
     */
    public JavaInputWithJMLSpecBrowser(String name, File path, 
            boolean allIntMode,  ProgressMonitor monitor) {
        super(name, path, monitor);
    }    
    
    public void read(ModStrategy mod) throws ProofInputException {
       //readProblem(mod);
    }
    
    public void readProblem(ModStrategy mod) throws ProofInputException {
        jmlPO = null;
        int option = JOptionPane.NO_OPTION;
        do {
            JMLSpecBrowser sb = 
                new JMLSpecBrowser(initConfig.getServices(), readJavaPath());
            jmlPO = sb.getPOI();
            if (jmlPO == null) {
                option = JOptionPane.showConfirmDialog
                (null, "Do you really want to abort loading the proof?", 
                        "Abort Loading", 
                        JOptionPane.YES_NO_OPTION);
            }
        } while (option == JOptionPane.NO_OPTION && jmlPO == null);
        
        if (jmlPO == null){
            if (option == JOptionPane.YES_OPTION) {
                throw ProofInputException.USER_ABORT_EXCEPTION;
            }
            throw new ProofInputException("No Proofobligation could be created.");
        } else {
            jmlPO.setInitConfig(getInitConfig());
        }
        try {
            jmlPO.readProblem(ModStrategy.NO_GENSORTS);
        } catch(ProofInputException e){           
            initConfig.getServices().getExceptionHandler().reportException(e);
        }
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.init.ProofOblInput#getPO()
     */
    public ProofAggregate getPO() {			
	return jmlPO.getPO();
    }
}
