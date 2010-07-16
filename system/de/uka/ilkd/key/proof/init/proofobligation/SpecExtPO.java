// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init.proofobligation;

import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.cspec.ComputeSpecification;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.OperationContract;

/**
 * This class is needed to use Key for extraction of additional information to
 * be used in jmltest
 *
 * @author mbender@uni-koblenz.de
 *
 */
public class SpecExtPO extends EnsuresPostPO {

    private ImmutableList<ProgramVariable> params;

    private ProgramVariable result;

    private ProgramVariable selfVarAsProgVar;

    private LogicVariable selfVarAsLogicVar;

    private ProgramVariable excVar;

     SpecExtPO(InitConfig initConfig, OperationContract contract,
            ImmutableSet<ClassInvariant> assumedInvs) {
        super(initConfig, "ExtractSpec", contract, assumedInvs);
    }

     SpecExtPO(InitConfig initConfig, OperationContract contract,
            ImmutableSet<ClassInvariant> assumedInvs, ProgramMethod pm) {
        this(initConfig, contract, assumedInvs);
    }

    protected Term getPostTerm(ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
            ProgramVariable exceptionVar, Map<Operator, Function/*atPre*/> atPreFunctions)
            throws ProofInputException {
        return TermBuilder.DF.func(ComputeSpecification.ACCUMULATOR);
    }

    public ProofAggregate getPO() {
        Proof[] proofs = super.getPO().getProofs();
        for (Proof proof : proofs) {
            if (proof.name().toString().equals(
                    "ExtractSpec of " + getProgramMethod())) {
                proof.setPO(this);
            }

        }
        return ProofAggregate.createProofAggregate(proofs, name);
    }

    public ImmutableList<ProgramVariable> getParams() {
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
