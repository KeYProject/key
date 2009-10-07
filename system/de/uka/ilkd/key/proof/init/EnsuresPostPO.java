// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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

import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.OperationContract;


/**
 * The "EnsuresPost" proof obligation.
 */
public class EnsuresPostPO extends EnsuresPO {

    private final OperationContract contract;

    public EnsuresPostPO(InitConfig initConfig,
                         String name,
                         OperationContract contract,
                         ImmutableSet<ClassInvariant> assumedInvs) {
        super(initConfig,
              name,
              contract.getProgramMethod(),
              contract.getModality(),
              assumedInvs,
              true);
        this.contract = contract;
    }


    public EnsuresPostPO(InitConfig initConfig, OperationContract contract,
            ImmutableSet<ClassInvariant> assumedInvs) {
        this(initConfig,
             "EnsuresPost ("
                 + contract.getProgramMethod() + ", "
                 + contract.getDisplayName() + ")",
             contract,
             assumedInvs);
    }


    protected Term getPreTerm(ProgramVariable selfVar,
                              ImmutableList<ProgramVariable> paramVars,
                              ProgramVariable resultVar,
                              ProgramVariable exceptionVar,
                              Map<Operator, Function/*atPre*/> atPreFunctions)
            throws ProofInputException {
        Term result = translatePre(contract, selfVar, toPV(paramVars));
        return result;
    }


    protected Term getPostTerm(ProgramVariable selfVar,
                               ImmutableList<ProgramVariable> paramVars,
                               ProgramVariable resultVar,
                               ProgramVariable exceptionVar,
                               Map<Operator, Function/*atPre*/> atPreFunctions)
            throws ProofInputException {
        Term result = translatePost(contract,
                                    selfVar,
                                    toPV(paramVars),
                                    resultVar,
                                    exceptionVar,
                                    atPreFunctions);

        return result;
    }


    public boolean implies(ProofOblInput po) {
        if(!(po instanceof EnsuresPostPO)) {
            return false;
        }
        EnsuresPostPO epPO = (EnsuresPostPO) po;
        return specRepos.splitContract(epPO.contract)
                        .subset(specRepos.splitContract(contract))
               && assumedInvs.subset(epPO.assumedInvs);
    }


    public boolean equals(Object o) {
        if(!(o instanceof EnsuresPostPO)) {
            return false;
        }
        EnsuresPostPO po = (EnsuresPostPO) o;
        return super.equals(po)
               && contract.equals(po.contract);
    }


    public int hashCode() {
        return super.hashCode() + contract.hashCode();
    }
}
