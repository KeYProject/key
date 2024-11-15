/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.mgt;

import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.rusty.Services;
import org.key_project.rusty.logic.TermBuilder;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.ProgramFunction;
import org.key_project.rusty.speclang.FunctionalOperationContract;
import org.key_project.util.collection.ImmutableSet;

public class SpecificationRepository {
    private final Services services;
    private final TermBuilder tb;

    private final Map<ProgramFunction, ImmutableSet<FunctionalOperationContract>> operationContracts =
        new LinkedHashMap<>();

    public SpecificationRepository(Services services) {
        this.services = services;
        tb = services.getTermBuilder();
    }

    public ImmutableSet<FunctionalOperationContract> getOperationContracts(ProgramFunction fn,
            Modality.RustyModalityKind modalityKind) {
        ImmutableSet<FunctionalOperationContract> result = getOperationContracts(fn);
        for (var contract : result) {
            if (!contract.getModalityKind().equals(modalityKind)) {
                result = result.remove(contract);
            }
        }
        return result;
    }

    private ImmutableSet<FunctionalOperationContract> getOperationContracts(ProgramFunction fn) {
        var result = operationContracts.get(fn);
        return result == null ? ImmutableSet.empty() : result;
    }
}
