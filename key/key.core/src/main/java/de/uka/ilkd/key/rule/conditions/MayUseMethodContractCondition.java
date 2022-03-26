// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.recoderext.ConstructorNormalformBuilder;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.mgt.ContractOrderManager;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.Contract;
import org.key_project.util.collection.ImmutableArray;

import java.util.Map;


public final class MayUseMethodContractCondition extends VariableConditionAdapter {

    private final String parameter;

    public MayUseMethodContractCondition(String parameter) {
        this.parameter = parameter;
    }

    @SuppressWarnings("unchecked")
    @Override
    public boolean check(SchemaVariable var,
                         SVSubstitute subst,
                         SVInstantiations svInst,
                         Services services) {

        Contract contract = services.getSpecificationRepository().getContractByName(parameter);

        if (!ContractOrderManager.isEnabled()) {
            return services.getProof().mgt().isContractApplicable(contract);
        } else {
            ContractOrderManager com = ContractOrderManager.getInstance();
            Contract user = services.getSpecificationRepository().getContractPOForProof(services.getProof()).getContract();
            switch (com.mayUse(user, contract)) {
                case FORBIDDEN: return false;
                case WITH_MEASURED_BY: return contract.hasMby();
                case UNRESTRICTED: return true;
            }
            throw new Error("unreachable");
        }
    }

    @Override
    public String toString () {
        return "\\mayUseMethodContract[\"" + parameter + "\"]";
    }
}