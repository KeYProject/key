/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.util.List;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.speclang.Contract;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for {@link ContractIndex} over the two-method fixture {@code C}.
 */
class ContractIndexTest {

    private static final String ONE_NAME = "C[C::one()].JML normal_behavior operation contract.0";
    private static final String TWO_NAME = "C[C::two()].JML normal_behavior operation contract.0";

    @Test
    @Timeout(120)
    void listsAllContractsInStableOrder() throws Exception {
        KeYEnvironment<?> environment = KeYEnvironment.load(Fixtures.indexKey());
        try {
            ContractIndex index = ContractIndex.fromEnvironment(environment);

            List<ContractIndex.Row> rows = index.list();
            assertThat(rows).hasSize(2);
            assertThat(rows).extracting(ContractIndex.Row::idx).containsExactly(0, 1);
            assertThat(rows).extracting(ContractIndex.Row::idx).isSorted();
            assertThat(rows).extracting(ContractIndex.Row::targetName)
                    .containsExactly("C::one", "C::two");
            assertThat(rows).extracting(ContractIndex.Row::name)
                    .containsExactly(ONE_NAME, TWO_NAME);
        } finally {
            environment.dispose();
        }
    }

    @Test
    @Timeout(120)
    void resolvesContractsByIndexAndName() throws Exception {
        KeYEnvironment<?> environment = KeYEnvironment.load(Fixtures.indexKey());
        try {
            ContractIndex index = ContractIndex.fromEnvironment(environment);

            assertThat(index.byIdx(0)).isPresent()
                    .get().extracting(Contract::getName).isEqualTo(ONE_NAME);
            assertThat(index.byIdx(1)).isPresent()
                    .get().extracting(Contract::getName).isEqualTo(TWO_NAME);
            assertThat(index.byIdx(2)).isEmpty();

            assertThat(index.byName(ONE_NAME)).isPresent()
                    .get().extracting(Contract::getName).isEqualTo(ONE_NAME);
            assertThat(index.byName("NoSuchContract")).isEmpty();

            assertThat(index.byNameAndIdx(TWO_NAME, 1)).isPresent();
            assertThat(index.byNameAndIdx(TWO_NAME, 0)).isEmpty();
        } finally {
            environment.dispose();
        }
    }

    @Test
    @Timeout(120)
    void orderIsStableAcrossReloads() throws Exception {
        KeYEnvironment<?> first = KeYEnvironment.load(Fixtures.indexKey());
        KeYEnvironment<?> second = KeYEnvironment.load(Fixtures.indexKey());
        try {
            assertThat(ContractIndex.fromEnvironment(first).list())
                    .isEqualTo(ContractIndex.fromEnvironment(second).list());
        } finally {
            first.dispose();
            second.dispose();
        }
    }
}
