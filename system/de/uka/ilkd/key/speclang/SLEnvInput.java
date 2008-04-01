// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import java.util.Arrays;
import java.util.Comparator;
import java.util.Set;

import de.uka.ilkd.key.gui.configuration.GeneralSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.JavaASTCollector;
import de.uka.ilkd.key.logic.op.ListOfProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.init.AbstractEnvInput;
import de.uka.ilkd.key.proof.init.ModStrategy;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.jml.JMLSpecExtractor;
import de.uka.ilkd.key.speclang.ocl.OCLSpecExtractor;


/** 
 * EnvInput for standalone specification language front ends.
 */
public class SLEnvInput extends AbstractEnvInput {
        
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    private static String getLanguage() {
        GeneralSettings gs 
            = ProofSettings.DEFAULT_SETTINGS.getGeneralSettings();
        if(gs.useJML() && gs.useOCL()) {
            return "JML/OCL";
        } else if(gs.useJML()) {
            return "JML";
        } else if(gs.useOCL()) {
            return "OCL";
        } else {
            return "no";
        }
    }
    
    
    public SLEnvInput(String javaPath) {
        super(getLanguage() + " specifications", javaPath);
        assert javaPath != null;
    }
    

    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private KeYJavaType[] sortKJTs(KeYJavaType[] kjts) {
        Arrays.sort(kjts, new Comparator<KeYJavaType> () {
            public int compare(KeYJavaType o1, KeYJavaType o2) {
                return o1.getFullName().compareTo(o2.getFullName());
            }
        });
        
        return kjts;
    }
    
    
    private void createSpecs(SpecExtractor specExtractor) 
            throws ProofInputException {
        JavaInfo javaInfo 
            = initConfig.getServices().getJavaInfo();
        SpecificationRepository specRepos 
            = initConfig.getServices().getSpecificationRepository();
       
        //sort types alphabetically (necessary for deterministic names)
        final Set<KeYJavaType> allKeYJavaTypes = javaInfo.getAllKeYJavaTypes();
        final KeYJavaType[] kjts = 
            sortKJTs(allKeYJavaTypes.toArray(new KeYJavaType[allKeYJavaTypes.size()]));
        
        //create specifications for all types
        for(int i = 0; i < kjts.length; i++) {
            final KeYJavaType kjt = kjts[i];
            
            //class invariants
            specRepos.addClassInvariants(
                        specExtractor.extractClassInvariants(kjt));
            
            //contracts, loop invariants
            ListOfProgramMethod pms 
                = javaInfo.getAllProgramMethodsLocallyDeclared(kjt);
            for(ProgramMethod pm : pms) {
                //contracts
                specRepos.addOperationContracts(
                            specExtractor.extractOperationContracts(pm));
                
                //loop invariants
                JavaASTCollector collector 
                    = new JavaASTCollector(pm.getBody(), LoopStatement.class);
                collector.start();
                for(ProgramElement loop : collector.getNodes()) {
                    LoopInvariant inv = specExtractor.extractLoopInvariant(
                	    			pm, 
                        			(LoopStatement) loop);
                    if(inv != null) {
                        specRepos.setLoopInvariant(inv);
                    }
                }
            }
        }
    }

    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    public void read(ModStrategy mod) throws ProofInputException {
        if(initConfig == null) {
            throw new IllegalStateException("InitConfig not set.");
        }
        
        GeneralSettings gs 
            = ProofSettings.DEFAULT_SETTINGS.getGeneralSettings();
        if(gs.useJML()) {
            createSpecs(new JMLSpecExtractor(initConfig.getServices()));
        }
        if(gs.useOCL()) {
            createSpecs(new OCLSpecExtractor(initConfig.getServices()));
        }
    }
}
