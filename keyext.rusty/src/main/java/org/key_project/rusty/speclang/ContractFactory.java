/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.speclang;

import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.TermBuilder;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.ProgramFunction;

public class ContractFactory {
    private final Services services;
    private final TermBuilder tb;

    /**
     * Creates a new contract factory.
     *
     * @param services the services object
     */
    public ContractFactory(Services services) {
        assert services != null;
        this.services = services;
        this.tb = services.getTermBuilder();
    }

    public static String generateContractName(String baseName, ProgramFunction target, int id) {
        return generateContractTypeName(baseName, target) + "." + id;
    }

    public static String generateContractTypeName(String baseName, ProgramFunction target) {
        final String fnName = target.name().toString();
        // final String methodShortName = fnName.substring(startIndexShortName);
        return fnName + "." + baseName;
    }

    /**
     * Creates a new functional operation contract.
     *
     * @param baseName base name of the contract (does not have to be unique)
     * @param fn the function to which the contract belongs
     * @param modalityKind the modality of the contract
     * @param pre the precondition of the contract
     * @param mby the measured_by clause of the contract
     * @param post the postcondition of the contract
     * @param modifiable the modifiable clause of the contract
     * @param progVars the program variables
     * @param toBeSaved TODO
     * @return the resulting functional operation contract
     */
    public FunctionalOperationContract func(String baseName, ProgramFunction fn,
            Modality.RustyModalityKind modalityKind,
            Term pre, Term mby,
            Term post,
            Term modifiable,
            ProgramVariableCollection progVars, boolean toBeSaved) {
        return new FunctionalOperationContractImpl(baseName, null, fn,
            modalityKind, pre, mby, post,
            modifiable,
            // progVars.selfVar,
            progVars.params(),
            progVars.result(), null, Contract.INVALID_ID,
            toBeSaved, services);
    }

    /**
     * Creates a new functional operation contract.
     *
     * @param baseName base name of the contract (does not have to be unique)
     * @param fn the function to which the contract belongs
     * @param terminates a boolean determining whether we also prove termination
     * @param pre the precondition of the contract
     * @param mby the measured_by clause of the contract
     * @param post the postcondition of the contract
     * @param modifiable the modifiable clause of the contract
     * @param progVars the program variables
     * @param toBeSaved TODO
     * @return the resulting functional operation contract
     */
    public FunctionalOperationContract func(String baseName, ProgramFunction fn,
            boolean terminates,
            Term pre, Term mby,
            Term post,
            Term modifiable,
            ProgramVariableCollection progVars, boolean toBeSaved) {
        return func(baseName, fn,
            terminates ? Modality.RustyModalityKind.DIA : Modality.RustyModalityKind.BOX, pre, mby,
            post, modifiable, progVars, toBeSaved);
    }
}
