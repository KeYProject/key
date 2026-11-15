/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.util.List;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.Contract;

import org.jspecify.annotations.Nullable;

/**
 * The default contract selection of a loaded KeY problem (§4.2 of the headless interface spec):
 * without {@code --choose-contract} selectors, the contract selected by the load file's
 * {@code \chooseContract}/{@code \proofObligation} directive is the selection, and if the load
 * file selects no contract all contracts of the problem are selected.
 * <p>
 * Shared by the {@code prove} and {@code script} subcommands so both fall back to the load file
 * and to the full index identically.
 */
public final class ObligationSelection {
    private ObligationSelection() {
    }

    /**
     * Returns the contract selected by a {@code \chooseContract}/{@code \proofObligation}
     * directive of the loaded problem, or {@code null} if the load file does not select a
     * contract (e.g. it defines a plain {@code \problem}).
     *
     * @param environment the loaded KeY environment
     * @return the contract selected by the load file, or {@code null} if the load file selects
     *         no contract
     */
    public static @Nullable Contract loadFileContract(KeYEnvironment<?> environment) {
        Proof loaded = environment.getLoadedProof();
        if (loaded == null) {
            return null;
        }
        ProofOblInput po =
            environment.getServices().getSpecificationRepository().getProofOblInput(loaded);
        return po instanceof ContractPO contractPO ? contractPO.getContract() : null;
    }

    /**
     * Returns the contracts selected by the load file's {@code \chooseContract}/
     * {@code \proofObligation} directive ({@link #loadFileContract}) as a single-element
     * selection, or all contracts of the problem if the load file selects none.
     *
     * @param environment the loaded KeY environment
     * @param index the stable index over the problem's contracts
     * @return the default selection, in stable index order
     */
    public static List<Contract> defaultSelection(KeYEnvironment<?> environment,
            ContractIndex index) {
        Contract loadFileContract = loadFileContract(environment);
        return loadFileContract != null ? List.of(loadFileContract) : index.contracts();
    }
}
