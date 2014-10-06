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
 * This class contains the set of four sets of ProofObligationVars necessary for
 * information flow proofs.
 * <p/>
 * @author christoph
 * <p/>
 */
public class IFProofObligationVars {

    public final ProofObligationVars c1, c2, symbExecVars;

    private final Map<ProofObligationVars, Map<Term, Term>> infFlowToSymbExecVarsMaps;


    public IFProofObligationVars(ProofObligationVars symbExecVars,
                                 Services services) {
        this(new ProofObligationVars(symbExecVars, "_A", services),
             new ProofObligationVars(symbExecVars, "_B", services),
             symbExecVars);
    }


    public IFProofObligationVars(ProofObligationVars c1,
                                  ProofObligationVars c2,
                                  ProofObligationVars symbExecVars) {
        this.c1 = c1;
        this.c2 = c2;
        this.symbExecVars = symbExecVars;

        assert symbExecVars != null;
        infFlowToSymbExecVarsMaps =
                new HashMap<ProofObligationVars, Map<Term, Term>>();
        infFlowToSymbExecVarsMaps.put(c1, new HashMap<Term, Term>());
        infFlowToSymbExecVarsMaps.put(c2, new HashMap<Term, Term>());
        linkSymbExecVarsToCopies();
    }


    public IFProofObligationVars labelHeapAtPreAsAnonHeapFunc() {
        ProofObligationVars newC1 = c1.labelHeapAtPreAsAnonHeapFunc();
        ProofObligationVars newC2 = c2.labelHeapAtPreAsAnonHeapFunc();
        ProofObligationVars sev = symbExecVars.labelHeapAtPreAsAnonHeapFunc();
        return new IFProofObligationVars(newC1, newC2, sev);
    }


    private void linkSymbExecVarsToCopies() {
        for (ProofObligationVars ifVars : infFlowToSymbExecVarsMaps.keySet()) {
            linkStateVarsToCopies(ifVars.pre, symbExecVars.pre, getMapFor(ifVars));
            linkStateVarsToCopies(ifVars.post, symbExecVars.post, getMapFor(ifVars));
        }
    }


    private void linkStateVarsToCopies(StateVars ifVars,
                                       StateVars seVars,
                                       Map<Term, Term> map) {
        final Iterator<Term> ifVarsIt = ifVars.termList.iterator();
        for (final Term symbTerm : seVars.termList) {
            final Term ifTerm = ifVarsIt.next();
            if (symbTerm != null) {
                map.put(symbTerm, ifTerm);
            }
        }
    }


    public Map<Term, Term> getMapFor(ProofObligationVars vars) {
        return infFlowToSymbExecVarsMaps.get(vars);
    }


    @Override
    public String toString() {
        return "[" + symbExecVars + "," + c1 + "," + c2 + "]";
    }
}