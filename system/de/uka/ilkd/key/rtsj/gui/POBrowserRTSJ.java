// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rtsj.gui;

import de.uka.ilkd.key.gui.ClassTree;
import de.uka.ilkd.key.gui.ContractConfigurator;
import de.uka.ilkd.key.gui.POBrowser;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rtsj.proof.init.proofobligation.RTSJPOProvider;

public class POBrowserRTSJ extends POBrowser {

    public POBrowserRTSJ(InitConfig initConfig, String title,
	    ProgramMethod defaultPm) {
	super(initConfig, title, defaultPm);
    }

    protected ProofOblInput createPO(ClassTree.Entry selectedEntry,
	    String poString) {
	if (poString.equals(RTSJPOProvider.RESPECTS_WORKING_SPACE)) {
	    assert selectedEntry.pm != null;
	    return createRespectsWorkingSpacePO(selectedEntry.pm);
	} else {
	    return super.createPO(selectedEntry, poString);
	}

    }

    private ProofOblInput createRespectsWorkingSpacePO(ProgramMethod pm) {
	ContractConfigurator cc = new ContractConfigurator(this, services, pm,
	        null, true, false, true, false);
	if (cc.wasSuccessful()) {
	    return ((RTSJPOProvider) poProvider).createRespectsWorkingSpacePO(
		    initConfig, cc.getContract(), cc.getAssumedInvs());
	} else {
	    return null;
	}
    }
}
