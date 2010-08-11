// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.proof.init.proofobligation;

import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.OperationContract;

public abstract class AbstractEnsuresPostPO extends EnsuresPO {

    protected final OperationContract contract;

    public AbstractEnsuresPostPO(InitConfig initConfig, String name,
	    OperationContract contract,
	    ImmutableSet<ClassInvariant> assumedInvs, boolean skipPreconditions) {
	super(initConfig, name, contract.getProgramMethod(), contract
	        .getModality(), assumedInvs, skipPreconditions);
	this.contract = contract;
    }

    protected Term getPreTerm(ProgramVariable selfVar,
	    ImmutableList<ProgramVariable> paramVars,
	    ProgramVariable resultVar, ProgramVariable exceptionVar,
	    Map<Operator, Function/* atPre */> atPreFunctions)
	    throws ProofInputException {
	Term result = translatePre(contract, selfVar, toPV(paramVars));
	return result;
    }

    protected Term getPostTerm(ProgramVariable selfVar,
	    ImmutableList<ProgramVariable> paramVars,
	    ProgramVariable resultVar, ProgramVariable exceptionVar,
	    Map<Operator, Function/* atPre */> atPreFunctions)
	    throws ProofInputException {
	Term result = translatePost(contract, selfVar, toPV(paramVars),
	        resultVar, exceptionVar, atPreFunctions);

	return result;
    }

    public OperationContract getContract() {
	return contract;
    }

}
