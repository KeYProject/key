// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.logic.op.ProgramMethod;


/**
 * The "PreservesOwnInv" proof obligation. 
 */
public class PreservesOwnInvPO extends PreservesInvPO {
    
    public PreservesOwnInvPO(InitConfig initConfig,
	    		     ProgramMethod programMethod) {
        super(initConfig,
              "PreservesOwnInv",
              programMethod, 
              initConfig.getServices()
                        .getSpecificationRepository()
                        .getClassInvariants(programMethod.getContainerType()),
              initConfig.getServices()
              	        .getSpecificationRepository()
              	        .getClassInvariants(programMethod.getContainerType()));
    }
}
