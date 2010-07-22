// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                          Universitaet Koblenz-Landau, Germany
//                          Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rtsj.proof.init.proofobligation;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.init.proofobligation.AbstractEnsuresPostPO;
import de.uka.ilkd.key.rtsj.proof.init.RTSJProfile;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.OperationContract;

/**
 * The "EnsuresPost" proof obligation.
 */
public class EnsuresPostPO extends AbstractEnsuresPostPO {

    EnsuresPostPO(InitConfig initConfig, String name,
	    OperationContract contract, ImmutableSet<ClassInvariant> assumedInvs) {
	super(initConfig, name, contract, assumedInvs, true);
	assert initConfig.getProfile() instanceof RTSJProfile;
    }

    EnsuresPostPO(InitConfig initConfig, OperationContract contract,
	    ImmutableSet<ClassInvariant> assumedInvs) {
	this(initConfig, "EnsuresPost (" + contract.getProgramMethod() + ", "
	        + contract.getDisplayName() + ")", contract, assumedInvs);
    }

    protected Term buildGeneralMemoryAssumption(ProgramVariable selfVar,
	    ImmutableList<ProgramVariable> paramVars)
	    throws ProofInputException {

	Term result = TB.tt();
	

	final ProgramVariable stack = services.getJavaInfo().getAttribute(
	        "stack", "javax.realtime.MemoryArea");
	ProgramVariable initialMemoryArea = services.getJavaInfo()
	        .getDefaultMemoryArea();
	Term t_mem = TB.var(initialMemoryArea);
	result = TB.and(result,
	        TB.not(TB.equals(TB.dot(t_mem, stack), TB.NULL(services))));

	Term initialMemCreatedAndNotNullTerm = CreatedAttributeTermFactory.INSTANCE
	        .createCreatedAndNotNullTerm(services, t_mem);
	result = TB.and(result, initialMemCreatedAndNotNullTerm);

	if (((RTSJProfile) initConfig.getProfile()).memoryConsumption()
	        && contract.getWorkingSpace(selfVar, toPV(paramVars), services) != null) {
	    final ProgramVariable size = services.getJavaInfo().getAttribute(
		    "size", "javax.realtime.MemoryArea");
	    final ProgramVariable consumed = services.getJavaInfo()
		    .getAttribute("consumed", "javax.realtime.MemoryArea");

	    Function add = services.getTypeConverter().getIntegerLDT().getAdd();
	    Function leq = services.getTypeConverter().getIntegerLDT()
		    .getLessOrEquals();

	    Term workingSpace = contract.getWorkingSpace(selfVar,
		    toPV(paramVars), services);
	    result = TB.and(result, TB.func(leq,
		    TB.func(add, TB.dot(t_mem, consumed), workingSpace),
		    TB.dot(t_mem, size)));
	}

	return result;
    }


    public boolean implies(ProofOblInput po) {
	if (!(po instanceof EnsuresPostPO)) {
	    return false;
	}
	EnsuresPostPO epPO = (EnsuresPostPO) po;
	return specRepos.splitContract(epPO.contract).subset(
	        specRepos.splitContract(contract))
	        && assumedInvs.subset(epPO.assumedInvs);
    }

    public boolean equals(Object o) {
	if (!(o instanceof EnsuresPostPO)) {
	    return false;
	}
	EnsuresPostPO po = (EnsuresPostPO) o;
	return super.equals(po) && contract.equals(po.contract);
    }

    public int hashCode() {
	return super.hashCode() + contract.hashCode();
    }

    public OperationContract getContract() {
	return contract;
    }
}
