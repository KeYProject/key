// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.casetool.together;

import java.util.Iterator;
import java.util.Vector;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.ListOfKeYJavaType;
import de.uka.ilkd.key.java.abstraction.SLListOfKeYJavaType;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.init.AbstractEnvInput;
import de.uka.ilkd.key.proof.init.ModStrategy;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.SetOfOperationContract;
import de.uka.ilkd.key.speclang.ocl.translation.OCLSpecFactory;



/** 
 * EnvInput for Together.
 */
public class TogetherEnvInput extends AbstractEnvInput {
    
    private final TogetherModelClass anyTogetherModelClass;
    private final boolean createSpecs;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    public TogetherEnvInput(TogetherModelClass anyTogetherModelClass,
	    	            boolean createSpecs) {
	super("Together input", anyTogetherModelClass.getRootDirectory());
	this.anyTogetherModelClass = anyTogetherModelClass;
	this.createSpecs           = createSpecs;
    }

    
    public TogetherEnvInput(TogetherModelClass anyTogetherModelClass) {
	this(anyTogetherModelClass, true);
    }

    
        
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private KeYJavaType getKJT(TogetherModelClass modelClass, 
	    		       JavaInfo javaInfo) {
	assert modelClass != null;
	
	KeYJavaType result 
		= javaInfo.getTypeByClassName(modelClass.getFullClassName());
	assert result != null : "KJT not found : \"" 
	    			+ modelClass.getFullClassName() + "\"";
	return result;
    }
    
    
    private ProgramMethod getProgramMethod(TogetherModelMethod modelMethod,
	    				   KeYJavaType containingClass,
	    				   JavaInfo javaInfo) {
	assert modelMethod != null;
	
	//collect signature KJTs
	ListOfKeYJavaType signature = SLListOfKeYJavaType.EMPTY_LIST;           
        for(int i = 0; i < modelMethod.getNumParameters(); i++) {
            String parTypeName = modelMethod.getParameterTypeAt(i);
            KeYJavaType kjt = javaInfo.getTypeByClassName(parTypeName);
            assert kjt != null : "KJT not found: \"" + parTypeName + "\"";
            signature = signature.append(kjt);
        }
        
        //determine name ("<init>" for constructors)
        String operationName 
        	= modelMethod.getName().equals(containingClass.getName())
        	  ? "<init>"
        	  : modelMethod.getName();

        //ask javaInfo
        ProgramMethod result 
        	= javaInfo.getProgramMethod(containingClass,
                               		    operationName,
                                            signature,
                                            containingClass);
        assert result != null : "ProgramMethod not found: \"" 
            			+ operationName + "\""
        			+ "\nsignature: " + signature
        			+ "\ncontainer: " + containingClass;
        return result;
    }
    
    
    private void createSpecs() 
            throws ProofInputException {
        Services services = initConfig.getServices();
	JavaInfo javaInfo 
                = services.getJavaInfo();
	SpecificationRepository specRepos 
                = services.getSpecificationRepository();
        OCLSpecFactory osf = new OCLSpecFactory(services);
        
        Iterator it = anyTogetherModelClass.getAllClasses().iterator();
	while(it.hasNext()) {
	    TogetherModelClass mc = (TogetherModelClass) it.next();
	    KeYJavaType kjt = getKJT(mc, javaInfo);
        
	    //class invariants
	    String invString = mc.getMyInv();
	    if(invString != null && !invString.equals("")) { 
                ClassInvariant inv = osf.createOCLClassInvariant(kjt, 
                                                                 invString);
		specRepos.addClassInvariant(inv);
	    }
	    
	    //operation contracts
	    Vector ops = mc.getOps();
	    Iterator it2 = ops.iterator();
	    while(it2.hasNext()) {
		TogetherModelMethod mm = (TogetherModelMethod) it2.next();
		ProgramMethod programMethod = getProgramMethod(mm, 
							       kjt, 
							       javaInfo);
		
		String preString      = mm.getMyPreCond();
		String postString     = mm.getMyPostCond();
		String modifiesString = mm.getMyModifClause();
                if(preString != null && !preString.equals("")
                   || postString != null && !postString.equals("") 
                   || modifiesString != null && !modifiesString.equals("")) {
                    SetOfOperationContract contracts
                        = osf.createOCLOperationContracts(programMethod, 
                                                          preString, 
                                                          postString, 
                                                          modifiesString);
                    specRepos.addOperationContracts(contracts);
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
	
	//create OCL specifications
	if(createSpecs) {
	    createSpecs();
	}
	
	//create UML info
	Services services = initConfig.getServices();
	services.setUMLInfo(anyTogetherModelClass.createUMLInfo(services));
    }
}
