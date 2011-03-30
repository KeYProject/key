// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.OperationContract;

public abstract class AbstractOperationContractPO extends AbstractPO
	implements ContractPO {

    protected Term mbyAtPre;

    
    
    public AbstractOperationContractPO(InitConfig initConfig, String name,
	    OperationContract contract) {
	super(initConfig, name, contract);
	// TODO Auto-generated constructor stub
    }

    
    public OperationContract getContract() {
	return (OperationContract)contract;
    }
    
    
    
    protected Term generateSelfNotNull(ProgramVariable selfVar) {
        return selfVar == null || getContract().getTarget().isConstructor()
              ? TB.tt()
              : TB.not(TB.equals(TB.var(selfVar), TB.NULL(services)));
    }

    
    protected Term generateSelfCreated(ProgramVariable selfVar) {
        return selfVar == null || getContract().getTarget().isConstructor()
             ? TB.tt()
             : TB.created(services, TB.var(selfVar));
    }

    
    protected Term generateSelfExactType(ProgramVariable selfVar, KeYJavaType selfKJT) {
        final Term selfExactType
           = selfVar == null || getContract().getTarget().isConstructor()
             ? TB.tt()
             : TB.exactInstance(services, 
        	                selfKJT.getSort(), 
        	                TB.var(selfVar));
        return selfExactType;
    }

    
    protected Term generateParamsOK(ImmutableList<ProgramVariable> paramVars) {
        Term paramsOK = TB.tt();
        for(ProgramVariable paramVar : paramVars) {
            paramsOK = TB.and(paramsOK, TB.reachableValue(services, paramVar));
        }
        return paramsOK;
    }

    
    protected Term generateMbyAtPreDef(ProgramVariable selfVar,
	    ImmutableList<ProgramVariable> paramVars) {
        final Term mbyAtPreDef;
        if(getContract().hasMby()) {
            final Function mbyAtPreFunc
            	= new Function(new Name(TB.newName(services, "mbyAtPre")), 
        		       services.getTypeConverter()
        		               .getIntegerLDT()
        		               .targetSort());
            register(mbyAtPreFunc);
            mbyAtPre = TB.func(mbyAtPreFunc);
            final Term mby = contract.getMby(selfVar, paramVars, services);
            mbyAtPreDef = TB.equals(mbyAtPre, mby);
        } else {
            mbyAtPreDef = TB.tt();
        }
        return mbyAtPreDef;
    }

}
