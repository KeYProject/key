/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.speclang.Contract;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for the default obligation selection of §4.2 of the headless interface spec
 * ({@link ObligationSelection}): the load file's {@code \chooseContract}/{@code \proofObligation}
 * directive selects its contract, and a load file without such a directive selects all
 * contracts of the stable index.
 */
class ObligationSelectionTest {

    private static final String ONE_NAME = "C[C::one()].JML normal_behavior operation contract.0";
    private static final String TWO_NAME = "C[C::two()].JML normal_behavior operation contract.0";

    @Test
    @Timeout(120)
    void chooseContractDirectiveSelectsTheNamedContract() throws Exception {
        KeYEnvironment<?> environment = KeYEnvironment.load(Fixtures.chooseKey());
        try {
            Contract contract =
                Objects.requireNonNull(ObligationSelection.loadFileContract(environment));
            assertThat(contract.getName()).isEqualTo(ONE_NAME);
        } finally {
            environment.dispose();
        }
    }

    @Test
    @Timeout(120)
    void proofObligationDirectiveSelectsTheNamedContract() throws Exception {
        KeYEnvironment<?> environment = KeYEnvironment.load(Fixtures.proofObligationKey());
        try {
            Contract contract =
                Objects.requireNonNull(ObligationSelection.loadFileContract(environment));
            assertThat(contract.getName()).isEqualTo(ONE_NAME);
        } finally {
            environment.dispose();
        }
    }

    @Test
    @Timeout(120)
    void plainProblemSelectsNoContract() throws Exception {
        KeYEnvironment<?> environment = KeYEnvironment.load(Fixtures.indexKey());
        try {
            assertThat(ObligationSelection.loadFileContract(environment)).isNull();
        } finally {
            environment.dispose();
        }
    }

    @Test
    @Timeout(120)
    void defaultSelectionFallsBackToAllIndexContracts() throws Exception {
        KeYEnvironment<?> environment = KeYEnvironment.load(Fixtures.indexKey());
        try {
            List<Contract> selected = ObligationSelection
                    .defaultSelection(environment, ContractIndex.fromEnvironment(environment));
            assertThat(selected).extracting(Contract::getName).containsExactly(ONE_NAME, TWO_NAME);
        } finally {
            environment.dispose();
        }
    }

    @Test
    @Timeout(120)
    void defaultSelectionSelectsOnlyTheDirectiveContract() throws Exception {
        KeYEnvironment<?> environment = KeYEnvironment.load(Fixtures.chooseKey());
        try {
            List<Contract> selected = ObligationSelection
                    .defaultSelection(environment, ContractIndex.fromEnvironment(environment));
            assertThat(selected).hasSize(1);
            assertThat(selected.get(0).getName()).isEqualTo(ONE_NAME);
        } finally {
            environment.dispose();
        }
    }
}
