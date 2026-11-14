/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.io;

import java.nio.file.Paths;
import java.util.Objects;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Regression test for the headless interface spec §4.2: both {@code \chooseContract} and
 * {@code \proofObligation} accept a plain contract name (the canonical name of
 * {@link de.uka.ilkd.key.speclang.Contract#getName()}) as their value, not only a serialized
 * proof obligation.
 */
class ProofObligationByNameTest {

    private static final String FIXTURE_DIR =
        "src/test/resources/de/uka/ilkd/key/proof/io/proofObligationByName";
    private static final String ONE_NAME = "C[C::one()].JML normal_behavior operation contract.0";

    @Test
    @Timeout(120)
    void loadByChosenContractName() throws ProblemLoaderException {
        KeYEnvironment<?> env = loadEnvironment("choose.key");
        try {
            assertThat(contractNameOfLoadedProof(env)).isEqualTo(ONE_NAME);
        } finally {
            env.dispose();
        }
    }

    @Test
    @Timeout(120)
    void loadByProofObligationName() throws ProblemLoaderException {
        KeYEnvironment<?> env = loadEnvironment("proofobl.key");
        try {
            assertThat(contractNameOfLoadedProof(env)).isEqualTo(ONE_NAME);
        } finally {
            env.dispose();
        }
    }

    private static KeYEnvironment<?> loadEnvironment(String keyFile) throws ProblemLoaderException {
        return KeYEnvironment.load(Paths.get(FIXTURE_DIR, keyFile), null, null, null);
    }

    private static String contractNameOfLoadedProof(KeYEnvironment<?> env) {
        Proof proof = env.getLoadedProof();
        assertThat(proof).isNotNull();
        ProofOblInput po = Objects.requireNonNull(
            env.getServices().getSpecificationRepository().getProofOblInput(proof));
        assertThat(po).isInstanceOf(ContractPO.class);
        return ((ContractPO) po).getContract().getName();
    }
}
