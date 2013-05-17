/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;


/**
 * This class contains the set of four sets of ProofObligationVars necessary
 * for information flow proofs.
 * <p/>
 * @author christoph
 * <p/>
 */
public class IFProofObligationVars {

    public final ProofObligationVars c1, c2, symbExecVars;

    public final Map<Term, Term> map1, map2;


    public IFProofObligationVars(ProofObligationVars symbExecVars,
                                 Services services,
                                 boolean local) {
        this(new ProofObligationVars(symbExecVars, "_A", services, local),
             new ProofObligationVars(symbExecVars, "_B", services, local),
             symbExecVars);
    }


    private IFProofObligationVars(ProofObligationVars c1,
                                  ProofObligationVars c2,
                                  ProofObligationVars symbExecVars) {
        this.c1 = c1;
        this.c2 = c2;
        this.symbExecVars = symbExecVars;

        map1 = new HashMap<Term, Term>();
        map2 = new HashMap<Term, Term>();

        if (symbExecVars != null) {
            linkSymbExecVarsToCopies(symbExecVars);
        }
    }


    private void linkSymbExecVarsToCopies(ProofObligationVars symbExecVars) {
        final Iterator<Term> c1It = c1.termList.iterator();
        final Iterator<Term> c2It = c2.termList.iterator();
        for (final Term symbTerm : symbExecVars.termList) {
            final Term c1Term = c1It.next();
            final Term c2Term = c2It.next();
            if (symbTerm != null) {
                map1.put(symbTerm, c1Term);
                map2.put(symbTerm, c2Term);
            }
        }
    }


    @Override
    public String toString() {
        return "[" + symbExecVars + "," + c1 + "," + c2 + "]";
    }
}