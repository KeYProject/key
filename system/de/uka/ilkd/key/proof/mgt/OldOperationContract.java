// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Proof;

/**
 * @deprecated
 */
public interface OldOperationContract extends Contract{

    String getPreText();

    String getPostText();
    
    String getModifiesText();
       
    String getHTMLText();

    Modality getModality();  
    
    boolean applicableForModality(Modality modality);
    
    ModelMethod getModelMethod();
    
    InstantiatedMethodContract instantiate(MethodContractInstantiation l, Proof proof, ExecutionContext ec);
   
    DLMethodContract createDLMethodContract(Proof proof);
    
}
