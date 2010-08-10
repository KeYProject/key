// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.proof.init.proofobligation;

import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.init.InitConfig;


/**
 * The "PreservesOwnInv" proof obligation.
 */
public class PreservesOwnInvPO extends PreservesInvPO {

    public PreservesOwnInvPO(InitConfig initConfig,
	    		     ProgramMethod programMethod) {
        super(initConfig,
              "PreservesOwnInv (" + programMethod + ")",
              programMethod,
              initConfig.getServices()
                        .getSpecificationRepository()
                        .getClassInvariants(programMethod.getContainerType()),
              initConfig.getServices()
              	        .getSpecificationRepository()
              	        .getClassInvariants(programMethod.getContainerType()));
    }
}
