package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

/**
 *
 * @author christoph
 */
interface SymbExecFactoryMethod {

    Term produce(SymbExecPOSnippetFactory f,
                 BasicSnippetData d,
                 ProofObligationVars poVars,
                 JavaInfo info)
            throws UnsupportedOperationException;
}
