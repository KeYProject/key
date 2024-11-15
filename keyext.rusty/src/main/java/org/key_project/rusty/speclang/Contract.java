/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.speclang;

import java.util.function.UnaryOperator;

import org.key_project.logic.Term;
import org.key_project.rusty.Services;

/**
 * A contractual agreement about an ObserverFunction.
 */
public interface Contract extends SpecificationElement {
    int INVALID_ID = Integer.MIN_VALUE;

    /**
     *
     * @return {@code true} if any only if this contract does not necessarily need to be proven in
     *         its own proof obligation. E.g., this is true for {@link FunctionalBlockContract}s and
     *         {@link FunctionalLoopContract}s.
     */
    default boolean isAuxiliary() {
        return false;
    }

    /**
     * Returns the id number of the contract. If a contract has instances for several methods
     * (inheritance!), all instances have the same id. The id is either non-negative or equal to
     * INVALID_ID.
     */
    int id();

    /**
     * Returns the contracted function symbol.
     */
    Object getTarget();

    /**
     * Tells whether the contract contains a measured_by clause.
     */
    boolean hasMby();

    Term getMby();

    /**
     * Returns the contract in pretty HTML format.
     *
     * @param services services instance
     * @return the html representation
     */
    String getHTMLText(Services services);

    /**
     * Returns the contract in pretty plain text format.
     *
     * @param services services instance
     * @return the plain text representation
     */
    String getPlainText(Services services);

    /**
     * Tells whether, on saving a proof where this contract is available, the contract should be
     * saved too. (this is currently true for contracts specified directly in DL, but not for JML
     * contracts)
     *
     * @return see above
     */
    boolean toBeSaved();

    @Override
    Contract map(UnaryOperator<Term> op, Services services);
}
