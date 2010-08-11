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


/**
 * The "PreservesThroughout" proof obligation.
 */
public class PreservesThroughoutPO extends EnsuresPO {

    private ImmutableSet<ClassInvariant> invs;

    public PreservesThroughoutPO(InitConfig initConfig,
	    			 ProgramMethod programMethod,
                                 ImmutableSet<ClassInvariant> invs) {
        super(initConfig,
              "PreservesThroughout (" + programMethod + ")",
              programMethod,
              Op.TOUT,
              invs,
              true);
        this.invs = invs;
    }


    protected Term getPreTerm(ProgramVariable selfVar,
                              ImmutableList<ProgramVariable> paramVars,
                              ProgramVariable resultVar,
                              ProgramVariable exceptionVar,
                              Map<Operator, Function/*atPre*/> atPreFunctions) throws ProofInputException {
        return TB.tt();
    }


    protected Term getPostTerm(ProgramVariable selfVar,
                               ImmutableList<ProgramVariable> paramVars,
                               ProgramVariable resultVar,
                               ProgramVariable exceptionVar,
                               Map<Operator, Function/*atPre*/> atPreFunctions) throws ProofInputException {
        return translateInvs(invs);
    }


    public boolean equals(Object o) {
        if(!(o instanceof PreservesThroughoutPO)) {
            return false;
        }
        PreservesThroughoutPO po = (PreservesThroughoutPO) o;
        return super.equals(po)
               && invs.equals(po.invs);
    }


    public int hashCode() {
        return super.hashCode() + invs.hashCode();
    }
}
