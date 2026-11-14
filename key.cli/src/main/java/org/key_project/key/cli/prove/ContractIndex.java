/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Optional;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.KeYTypeUtil;

/**
 * A stable index over the contracts of a loaded KeY problem.
 * <p>
 * The contracts are filtered to exclude library classes and sorted by their canonical name, so
 * that the ordinal ({@code idx}) of a row is deterministic across runs and hosts for identical
 * inputs. This is the basis for the listing and selection surfaces of the headless interface
 * contract (§4).
 */
public final class ContractIndex {

    /**
     * One row of the contract listing.
     *
     * @param idx the ordinal of the contract in the stable index
     * @param targetName the "Method:" line text KeY prints, e.g. {@code C::one}
     * @param name the canonical contract name, e.g.
     *        {@code C[C::one()].JML normal_behavior operation contract.0}
     */
    public record Row(int idx, String targetName, String name) {
    }

    private final List<Contract> contracts;
    private final List<Row> rows;

    /**
     * Creates an index over the given contracts, dropping library-class contracts and sorting the
     * remainder by canonical contract name.
     *
     * @param contracts the contracts to index (e.g. from
     *        {@code SpecificationRepository.getAllContracts()})
     */
    public ContractIndex(Iterable<Contract> contracts) {
        List<Contract> filtered = new ArrayList<>();
        for (Contract contract : contracts) {
            if (!KeYTypeUtil.isLibraryClass(contract.getKJT())) {
                filtered.add(contract);
            }
        }
        filtered.sort(Comparator.comparing(Contract::getName));
        this.contracts = List.copyOf(filtered);

        List<Row> newRows = new ArrayList<>(this.contracts.size());
        for (int i = 0; i < this.contracts.size(); i++) {
            Contract contract = this.contracts.get(i);
            newRows.add(new Row(i, contract.getTarget().name().toString(), contract.getName()));
        }
        this.rows = List.copyOf(newRows);
    }

    /**
     * Creates an index for the contracts of the given loaded environment.
     *
     * @param environment the loaded KeY environment
     * @return the contract index
     */
    public static ContractIndex fromEnvironment(KeYEnvironment<?> environment) {
        return new ContractIndex(
            environment.getServices().getSpecificationRepository().getAllContracts());
    }

    /**
     * Returns the rows of the listing.
     *
     * @return an immutable list of rows in stable order
     */
    public List<Row> list() {
        return rows;
    }

    /**
     * Returns the indexed contracts in stable order.
     *
     * @return an immutable list of contracts
     */
    public List<Contract> contracts() {
        return contracts;
    }

    /**
     * Returns the number of indexed contracts.
     *
     * @return the size of the index
     */
    public int size() {
        return contracts.size();
    }

    /**
     * Returns the contract with the given canonical name, if any.
     *
     * @param name the canonical contract name
     * @return the first matching contract, or empty if no contract has this name
     */
    public Optional<Contract> byName(String name) {
        return contracts.stream().filter(c -> c.getName().equals(name)).findFirst();
    }

    /**
     * Returns the contract at the given index.
     *
     * @param idx the ordinal
     * @return the contract, or empty if the index is out of range
     */
    public Optional<Contract> byIdx(int idx) {
        return idx >= 0 && idx < contracts.size() ? Optional.of(contracts.get(idx))
                : Optional.empty();
    }

    /**
     * Returns the contract at the given index if it also has the given canonical name. This
     * disambiguates overloads that share a canonical name.
     *
     * @param name the canonical contract name
     * @param idx the ordinal
     * @return the matching contract, or empty if the index or name does not match
     */
    public Optional<Contract> byNameAndIdx(String name, int idx) {
        return byIdx(idx).filter(contract -> contract.getName().equals(name));
    }
}
