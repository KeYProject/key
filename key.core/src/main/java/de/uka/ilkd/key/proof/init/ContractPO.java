/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.speclang.Contract;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * An obligation for some kind of contract.
 */
@NullMarked
public interface ContractPO extends ProofOblInput {

    Contract getContract();

    /**
     * @return the measured-by term at the precondition, or {@code null} if the contract has no
     *         measured-by clause
     */
    @Nullable
    JTerm getMbyAtPre();
}
