// This file is part of KeY - Integrated Deductive Software Design
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

import de.uka.ilkd.key.cspec.ComputeSpecification;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SetOfClassInvariant;

/**
 * This class is needed to use Key for extraction of additional information to
 * be used in jmltest
 * 
 * @author mbender@uni-koblenz.de
 * 
 */
public class SpecExtPO extends EnsuresPostPO {

    private ListOfProgramVariable params;

    private ProgramVariable result;

    private ProgramVariable selfVarAsProgVar;

    private LogicVariable selfVarAsLogicVar;

    private ProgramVariable excVar;

    public SpecExtPO(InitConfig initConfig, OperationContract contract,
            SetOfClassInvariant assumedInvs) {
        super(initConfig, "ExtractSpec", contract, assumedInvs);
    }

    public SpecExtPO(InitConfig initConfig, OperationContract contract,
            SetOfClassInvariant assumedInvs, ProgramMethod pm) {
        this(initConfig, contract, assumedInvs);
    }

    protected Term getPostTerm(ProgramVariable selfVar,
            ListOfProgramVariable paramVars, ProgramVariable resultVar,
            ProgramVariable exceptionVar, Map<Operator, Function/*atPre*/> atPreFunctions)
            throws ProofInputException {
        return TermBuilder.DF.func(ComputeSpecification.ACCUMULATOR);
    }

    public ProofAggregate getPO() {
        Proof[] proofs = super.getPO().getProofs();
        for (int i = 0; i < proofs.length; i++) {
            if (proofs[i].name().toString().equals(
                    "ExtractSpec of " + getProgramMethod())) {
                proofs[i].setPO(this);
            }

        }
        return ProofAggregate.createProofAggregate(proofs, name);
    }

    protected ListOfProgramVariable buildParamVars(ProgramMethod programMethod) {
        return params = super.buildParamVars(programMethod);
    }

    protected ProgramVariable buildResultVar(ProgramMethod programMethod) {
        return result = super.buildResultVar(programMethod);
    }

    protected ProgramVariable buildSelfVarAsProgVar() {
        return selfVarAsProgVar = super.buildSelfVarAsProgVar();
    }

    protected LogicVariable buildSelfVarAsLogicVar() {
        return selfVarAsLogicVar = super.buildSelfVarAsLogicVar();
    }

    protected ProgramVariable buildExcVar() {
        return excVar = super.buildExcVar();
    }

    public ListOfProgramVariable getParams() {
        return params;
    }

    public ProgramVariable getResult() {
        return result;
    }

    public ProgramVariable getSelfVarAsProgVar() {
        return selfVarAsProgVar;
    }

    public LogicVariable getSelfVarAsLogicVar() {
        return selfVarAsLogicVar;
    }

    public ProgramVariable getExcVar() {
        return excVar;
    }

}
