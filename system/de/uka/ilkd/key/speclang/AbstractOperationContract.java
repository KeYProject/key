//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.ListOfKeYJavaType;
import de.uka.ilkd.key.java.abstraction.SLListOfKeYJavaType;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramMethod;


public abstract class AbstractOperationContract implements OperationContract {
    protected static final TermBuilder tb = TermBuilder.DF;
    private final ModelMethod modelMethod;
    private final Modality modality;
    
    
    public AbstractOperationContract(ModelMethod modelMethod, 
	    			     Modality modality) {
	this.modelMethod = modelMethod;
	this.modality    = modality;
    }
    
    
    public ModelMethod getModelMethod() {
	return modelMethod;
    }
    
    
    public ProgramMethod getProgramMethod(Services services) {
    	JavaInfo javaInfo = services.getJavaInfo();
    	
    	String containingClassName = modelMethod.getContainingClassName();
    	KeYJavaType containingClass 
    		= javaInfo.getKeYJavaTypeByClassName(containingClassName);
    	
    	ListOfKeYJavaType signature = SLListOfKeYJavaType.EMPTY_LIST;    	
    	for(int i=0; i < modelMethod.getNumParameters(); i++) {
    	    String parTypeName = modelMethod.getParameterTypeAt(i);
    	    signature = signature.append(javaInfo.getKeYJavaType(parTypeName));
    	}
    	
    	return javaInfo.getProgramMethod(containingClass,
    					 modelMethod.getName(),
    					 signature,
    					 javaInfo.getJavaLangObject());
    }
    
    
    public Modality getModality() {
	return modality;
    }
}
