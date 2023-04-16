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
