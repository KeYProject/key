/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.speclang.Contract;


/**
 * An obligation for some kind of contract.
 */
public interface ContractPO extends ProofOblInput {

    Contract getContract();

    Term getMbyAtPre();
}
