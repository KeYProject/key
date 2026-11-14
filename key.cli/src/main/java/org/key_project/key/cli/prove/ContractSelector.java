/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.speclang.Contract;

/**
 * Resolves {@code --choose-contract} selector values (§4.2 of the headless interface spec)
 * against a {@link ContractIndex}:
 * <ul>
 * <li>a bare non-negative integer selects the row with that ordinal ({@link ContractIndex#byIdx}),
 * <li>a value of the form {@code NAME.#<IDX>} selects the row at ordinal {@code <IDX>} only if it
 * has the name {@code NAME} ({@link ContractIndex#byNameAndIdx}),
 * <li>any other value selects <em>all</em> rows with that exact canonical name (multi-set
 * semantics, §4.4).
 * </ul>
 * The selection order is the order in which the selectors were given.
 */
public final class ContractSelector {
    private ContractSelector() {
    }

    /**
     * Resolves all given selectors against the index.
     *
     * @param index the index to resolve against
     * @param selectors the selector values in command-line order
     * @return the selected contracts in selection order (one entry per matched row)
     * @throws UnknownContractException if any selector matches no contract
     */
    public static List<Contract> resolve(ContractIndex index, List<String> selectors)
            throws UnknownContractException {
        List<Contract> selected = new ArrayList<>();
        for (String selector : selectors) {
            List<Contract> match = resolveOne(index, selector);
            if (match.isEmpty()) {
                throw new UnknownContractException(selector, index);
            }
            selected.addAll(match);
        }
        return selected;
    }

    private static List<Contract> resolveOne(ContractIndex index, String selector) {
        int qualifier = qualifierPosition(selector);
        if (qualifier >= 0) {
            String name = selector.substring(0, qualifier);
            int idx = parseIndex(selector, qualifier + 2);
            return idx < 0 ? List.of()
                    : index.byNameAndIdx(name, idx).<List<Contract>>map(List::of).orElse(List.of());
        }
        if (isBareIndex(selector)) {
            int idx = parseIndex(selector, 0);
            return idx < 0 ? List.of()
                    : index.byIdx(idx).<List<Contract>>map(List::of).orElse(List.of());
        }
        return index.byNames(selector);
    }

    /**
     * Parses the decimal index starting at {@code from}, treating a value that does not fit into an
     * {@code int} as "no such index" instead of letting {@link NumberFormatException} escape as an
     * internal error.
     *
     * @param selector the selector text to read the digits from
     * @param from the first digit position inside the selector
     * @return the parsed index, or {@code -1} if the digits do not denote an index that can exist
     */
    private static int parseIndex(String selector, int from) {
        try {
            return Integer.parseInt(selector.substring(from));
        } catch (NumberFormatException e) {
            return -1;
        }
    }

    /**
     * Returns the position of the {@code '.'} of the {@code '.#'} qualifier that separates the
     * name from the ordinal in a {@code NAME.#<IDX>} selector, or {@code -1} if the selector is
     * not qualified.
     */
    private static int qualifierPosition(String selector) {
        int hash = selector.indexOf('#');
        if (hash < 2 || selector.charAt(hash - 1) != '.') {
            return -1;
        }
        String ordinal = selector.substring(hash + 1);
        if (ordinal.isEmpty() || !ordinal.chars().allMatch(Character::isDigit)) {
            return -1;
        }
        return hash - 1;
    }

    private static boolean isBareIndex(String selector) {
        return !selector.isEmpty() && selector.chars().allMatch(Character::isDigit);
    }
}
