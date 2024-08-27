/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.FinalHeapResolver;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import org.key_project.logic.Name;

public class FinalFieldsPOExtension implements POExtension {

    private static final Choice FINAL_IMMUTABLE_CHOICE = new Choice("finalFields", "immutable");

    @Override
    public boolean isPOSupported(ProofOblInput po) {
        if (po instanceof FunctionalOperationContractPO) {
            FunctionalOperationContractPO fpo = (FunctionalOperationContractPO) po;
            return fpo.getProgramMethod().isConstructor();
        }
        return false;
    }

    @Override
    public Term modifyPostTerm(AbstractOperationPO abstractPO, InitConfig proofConfig, Services services, ProgramVariable selfVar,
                               Term postTerm) {

        if(!FinalHeapResolver.isFinalEnabled(proofConfig)) {
            return postTerm;
        }

        // We know this holds because of isPOSupported:
        FunctionalOperationContractPO fpo = (FunctionalOperationContractPO) abstractPO;
        IProgramMethod constructor = fpo.getProgramMethod();
        assert constructor.isConstructor();

        FinalFieldCodeValidator.validateFinalFields(constructor, proofConfig);

        TermBuilder tb = services.getTermBuilder();
        LogicVariable fv = new LogicVariable(new Name("o"),
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
