// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License.
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init.proofobligation;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ModStrategy;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.OperationContract;


/**
 * The "StrongOperationContract" proof obligation.
 */
public class StrongOperationContractPO extends AbstractPO {

    private final OperationContract contract;
    private final ImmutableSet<ClassInvariant> assumedInvs;
    private final ImmutableSet<ClassInvariant> ensuredInvs;



    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    StrongOperationContractPO(InitConfig initConfig,
	    			     OperationContract contract,
                                     ImmutableSet<ClassInvariant> assumedInvs,
                                     ImmutableSet<ClassInvariant> ensuredInvs) {
        super(initConfig,
              "StrongOperationContract of " + contract.getProgramMethod(),
              contract.getProgramMethod().getContainerType());
        this.contract    = contract;
        this.assumedInvs = assumedInvs;
        this.ensuredInvs = ensuredInvs;
    }



    //-------------------------------------------------------------------------
    //methods of ProofOblInput interface
    //-------------------------------------------------------------------------

    public void readProblem(ModStrategy mod) throws ProofInputException {
        //prepare variables and container for @pre-functions
        ProgramMethod programMethod     = contract.getProgramMethod();
        ProgramVariable selfVar         = buildSelfVarAsProgVar();
        ImmutableList<ProgramVariable> paramVars = buildParamVars(programMethod);
        ProgramVariable resultVar       = buildResultVar(programMethod);
        ProgramVariable exceptionVar    = buildExcVar();
        Map<Operator, Function/*atPre*/> atPreFunctions =
            new LinkedHashMap<Operator, Function/*atPre*/>();

        //translate precondition
        Term preTerm = translatePre(contract, selfVar, toPV(paramVars));

        //translate and conjoin assumed invariants
        Term assumedInvsTerm = translateInvs(assumedInvs);

        //translate postcondition
        Term postTerm = translatePost(contract,
                                      selfVar,
                                      toPV(paramVars),
                                      resultVar,
                                      exceptionVar,
                                      atPreFunctions);

        //translate and conjoin ensured invariants
        Term ensuredInvsTerm = translateInvs(ensuredInvs);

        //build post implication with updates
        Term postImpTerm = TB.imp(postTerm, ensuredInvsTerm);
        Term postUpdateTerm = translateModifies(contract,
                                                postImpTerm,
                                                selfVar,
                                                toPV(paramVars));

        //build definitions for @pre-functions
        Update atPreDefinitions
            = APF.createAtPreDefinitions(atPreFunctions, services);

        //put everyhing together
        Term poTerm = TB.imp(TB.and(preTerm, assumedInvsTerm),
                             uf.apply(atPreDefinitions, postUpdateTerm));
        poTerms = new Term[]{poTerm};

        //register everything in namespaces
        registerInNamespaces(selfVar);
        registerInNamespaces(paramVars);
        registerInNamespaces(resultVar);
        registerInNamespaces(exceptionVar);
        registerInNamespaces(atPreFunctions);
    }
}
