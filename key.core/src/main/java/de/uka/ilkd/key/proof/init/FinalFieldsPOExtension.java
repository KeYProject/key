/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.ldt.FinalHeapResolution;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;

import org.key_project.logic.Choice;
import org.key_project.logic.op.Function;

/**
 * This class is responsible for making the immutable treatment of final fields possible also for
 * constructors.
 * It is an extension of the ProofOblInput interface (originally targeted for the symbolic execution
 * engine)
 * <p>
 * It has two purposes:
 * 1. It checks if the final fields are not read before they are written (via
 * {@link FinalFieldCodeValidator}).
 * 2. It modifies the postcondition of the constructor to make the final field values available in
 * the postconditions.
 * </p>
 * <p>
 * To make 2 possible, an additional premiss is added in the post-state formulating that
 * \forall Fields f; any::final(self, f) = any::select(heap, self, f)
 * essentially activating the final field assignments.
 * </p>
 *
 * @author Mattias Ulbrich
 */
public class FinalFieldsPOExtension implements POExtension {

    private static final Choice FINAL_IMMUTABLE_CHOICE = new Choice("finalFields", "immutable");

    @Override
    public boolean isPOSupported(ProofOblInput po) {
        if (po instanceof FunctionalOperationContractPO fpo) {
            return fpo.getProgramMethod().isConstructor();
        }
        return false;
    }

    @Override
    public JTerm modifyPostTerm(AbstractOperationPO abstractPO, InitConfig proofConfig,
            Services services, ProgramVariable selfVar,
            JTerm postTerm) {

        if (!FinalHeapResolution.isFinalEnabled(proofConfig)) {
            return postTerm;
        }

        // We know this holds because of isPOSupported:
        FunctionalOperationContractPO fpo = (FunctionalOperationContractPO) abstractPO;
        IProgramMethod iconstructor = fpo.getProgramMethod();
        assert iconstructor instanceof ProgramMethod
                : "Expected a ProgramMethod not a schema variable, since we need the actual implementation";
        ProgramMethod constructor = (ProgramMethod) iconstructor;

        List<Function> finalFields = findFinalFields(iconstructor, services);
        if (finalFields.isEmpty()) {
            // If there are no final fields, we do not need to do anything
            return postTerm;
        }

        FinalFieldCodeValidator.validateFinalFields(constructor, proofConfig);

        TermBuilder tb = services.getTermBuilder();
        JTerm self = tb.var(selfVar);
        for (Function finalField : finalFields) {
            JTerm fieldRef = tb.tf().createTerm(finalField);
            JTerm sel = tb.dot(JavaDLTheory.ANY, self, fieldRef);
            JTerm fsel = tb.finalDot(JavaDLTheory.ANY, self, fieldRef);
            JTerm eq = tb.equals(sel, fsel);
            postTerm = tb.imp(eq, postTerm);
        }
        return postTerm;
    }

    private List<Function> findFinalFields(IProgramMethod iconstructor, Services services) {
        Type type = iconstructor.getContainerType().getJavaType();
        assert type instanceof ClassType
                : "Class type was expected here, since a constructor is present";
        ClassType classType = (ClassType) type;
        return classType.getAllFields(services).filter(v -> v.isFinal() && !v.isModel())
                .map(f -> services.getTypeConverter().getHeapLDT()
                        .getFieldSymbolForPV((LocationVariable) f.getProgramVariable(), services))
                .toList();
    }


}
