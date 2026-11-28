/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

/**
 * Signals that a {@code --choose-contract} selector does not match any contract of the loaded
 * problem. Carries the offending selector and the {@link ContractIndex} so the caller can print
 * the full listing on stdout as demanded by §4.4 of the headless interface spec.
 *
 * @param selector the selector value that could not be resolved
 * @param index the contract index the selector was resolved against
 */
public final class UnknownContractException extends Exception {
    private final transient String selector;
    private final transient ContractIndex index;

    public UnknownContractException(String selector, ContractIndex index) {
        super("contract '" + selector + "' not found");
        this.selector = selector;
        this.index = index;
    }

    /**
     * Returns the selector that could not be resolved.
     *
     * @return the unknown selector value, verbatim
     */
    public String selector() {
        return selector;
    }

    /**
     * Returns the contract index the selector was resolved against.
     *
     * @return the index used for resolution
     */
    public ContractIndex index() {
        return index;
    }
}
