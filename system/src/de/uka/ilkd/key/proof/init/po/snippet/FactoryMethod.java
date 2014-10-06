package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

/**
 *
 * @author christoph
 */
interface FactoryMethod {

    Term produce(BasicSnippetData d,
                 ProofObligationVars poVars)
            throws UnsupportedOperationException;
}
