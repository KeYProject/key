/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.speclang.LoopSpecification;
import org.jspecify.annotations.NonNull;


/**
 *
 * @author christoph
 */
public class POSnippetFactory {

    public static @NonNull BasicPOSnippetFactory getBasicFactory(@NonNull FunctionalOperationContract contract,
                                                                 ProofObligationVars vars, @NonNull Services services) {
        return new BasicPOSnippetFactoryImpl(contract, vars, services);
    }

    public static @NonNull BasicPOSnippetFactory getBasicFactory(@NonNull LoopSpecification invariant,
                                                                 ProofObligationVars vars, ExecutionContext context, Term guardTerm, @NonNull Services services) {
        return new BasicPOSnippetFactoryImpl(invariant, vars, context, guardTerm, services);
    }

    public static @NonNull BasicPOSnippetFactory getBasicFactory(@NonNull InformationFlowContract contract,
                                                                 ProofObligationVars vars, @NonNull Services services) {
        return new BasicPOSnippetFactoryImpl(contract, vars, services);
    }

    public static @NonNull BasicPOSnippetFactory getBasicFactory(@NonNull BlockContract contract,
                                                                 ProofObligationVars vars, ExecutionContext context, @NonNull Services services) {
        return new BasicPOSnippetFactoryImpl(contract, vars, context, services);
    }

    static @NonNull BasicPOSnippetFactory getBasicFactory(BasicSnippetData data,
                                                          ProofObligationVars poVars) {
        return new BasicPOSnippetFactoryImpl(data, poVars);
    }

    public static @NonNull InfFlowPOSnippetFactory getInfFlowFactory(@NonNull LoopSpecification invariant,
                                                                     @NonNull ProofObligationVars vars1, @NonNull ProofObligationVars vars2, ExecutionContext context,
                                                                     Term guardTerm, @NonNull Services services) {
        return new InfFlowPOSnippetFactoryImpl(invariant, vars1, vars2, context, guardTerm,
            services);
    }

    public static @NonNull InfFlowPOSnippetFactory getInfFlowFactory(@NonNull InformationFlowContract contract,
                                                                     @NonNull ProofObligationVars vars1, @NonNull ProofObligationVars vars2, @NonNull Services services) {
        return new InfFlowPOSnippetFactoryImpl(contract, vars1, vars2, services);
    }

    public static @NonNull InfFlowPOSnippetFactory getInfFlowFactory(@NonNull BlockContract contract,
                                                                     @NonNull ProofObligationVars vars1, @NonNull ProofObligationVars vars2, ExecutionContext context,
                                                                     @NonNull Services services) {
        return new InfFlowPOSnippetFactoryImpl(contract, vars1, vars2, context, services);
    }

    static @NonNull InfFlowPOSnippetFactory getInfFlowFactory(BasicSnippetData data,
                                                              @NonNull ProofObligationVars vars1, @NonNull ProofObligationVars vars2) {
        return new InfFlowPOSnippetFactoryImpl(data, vars1, vars2);
    }
}
