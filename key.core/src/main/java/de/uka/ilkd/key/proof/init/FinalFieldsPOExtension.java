/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.FinalHeapResolution;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import org.key_project.logic.Name;

/**
 * This class is responsible for making the immutable treatment of final fields possible also for constructors.
 * It is an extension of the ProofOblInput interface (originally targeted for the symbolic execution engine)
 *
 * It has two purposes:
 * 1. It checks if the final fields are not read before they are written (via {@link FinalFieldCodeValidator}).
 * 2. It modifies the postcondition of the constructor to make the final field values available in the postconditions.
 *
 * To make 2 possible, an additional premiss is added in the post-state formulating that
 *    \forall Fields f; any::final(self, f) = any::select(heap, self, f)
 * essentially activating the final field assignments.
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
    public Term modifyPostTerm(AbstractOperationPO abstractPO, InitConfig proofConfig, Services services, ProgramVariable selfVar,
                               Term postTerm) {

        if(!FinalHeapResolution.isFinalEnabled(proofConfig)) {
            return postTerm;
        }

        // We know this holds because of isPOSupported:
        FunctionalOperationContractPO fpo = (FunctionalOperationContractPO) abstractPO;
        IProgramMethod iconstructor = fpo.getProgramMethod();
        assert iconstructor instanceof ProgramMethod : "Contracts cannot have schema ";
        ProgramMethod constructor = (ProgramMethod) iconstructor;

        FinalFieldCodeValidator.validateFinalFields(constructor, proofConfig);

        TermBuilder tb = services.getTermBuilder();
        LogicVariable fv = new LogicVariable(new Name("fld"),
            services.getTypeConverter().getHeapLDT().getFieldSort());
        Term self = tb.var(selfVar);
        Term sel = tb.dot(JavaDLTheory.ANY, self, tb.var(fv));
        Term fsel = tb.finalDot(JavaDLTheory.ANY, self, tb.var(fv));
        Term eq = tb.equals(sel, fsel);
        Term all = tb.all(List.of(fv), eq);
        Term imp = tb.imp(all, postTerm);
        return imp;
    }
}
