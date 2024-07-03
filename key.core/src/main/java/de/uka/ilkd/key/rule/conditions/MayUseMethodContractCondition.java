/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.mgt.ContractOrderManager;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.Contract;



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
            Contract user = services.getSpecificationRepository()
                    .getContractPOForProof(services.getProof()).getContract();
            switch (com.mayUse(user, contract)) {
            case FORBIDDEN:
                return false;
            case WITH_MEASURED_BY:
                return contract.hasMby();
            case UNRESTRICTED:
                return true;
            }
            throw new Error("unreachable");
        }
    }

    @Override
    public String toString() {
        return "\\mayUseMethodContract[\"" + parameter + "\"]";
    }
}
