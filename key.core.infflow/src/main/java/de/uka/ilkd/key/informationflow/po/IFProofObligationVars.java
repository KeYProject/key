/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.informationflow.ProofObligationVars;
import de.uka.ilkd.key.informationflow.proof.init.StateVars;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;


/**
 * This class contains the set of four sets of ProofObligationVars necessary for information flow
 * proofs.
 *
 * @author christoph
 *
 */
public class IFProofObligationVars {

    public final ProofObligationVars c1, c2, symbExecVars;

    private final Map<ProofObligationVars, Map<JTerm, JTerm>> infFlowToSymbExecVarsMaps;


    public IFProofObligationVars(ProofObligationVars symbExecVars, Services services) {
        this(new ProofObligationVars(symbExecVars, "_A", services),
            new ProofObligationVars(symbExecVars, "_B", services), symbExecVars);
    }


    public IFProofObligationVars(ProofObligationVars c1, ProofObligationVars c2,
            ProofObligationVars symbExecVars) {
        this.c1 = c1;
        this.c2 = c2;
        this.symbExecVars = symbExecVars;

        assert symbExecVars != null;
        infFlowToSymbExecVarsMaps = new HashMap<>();
        infFlowToSymbExecVarsMaps.put(c1, new HashMap<>());
        infFlowToSymbExecVarsMaps.put(c2, new HashMap<>());
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


    private void linkStateVarsToCopies(StateVars ifVars, StateVars seVars, Map<JTerm, JTerm> map) {
        final Iterator<JTerm> ifVarsIt = ifVars.termList.iterator();
        for (final JTerm symbTerm : seVars.termList) {
            final JTerm ifTerm;
            if (ifVarsIt.hasNext()) {
                ifTerm = ifVarsIt.next();
            } else {
                ifTerm = null;
            }
            if (symbTerm != null) {
                map.put(symbTerm, ifTerm);
            }
        }
    }


    public Map<JTerm, JTerm> getMapFor(ProofObligationVars vars) {
        return infFlowToSymbExecVarsMaps.get(vars);
    }


    @Override
    public String toString() {
        return "[" + symbExecVars + "," + c1 + "," + c2 + "]";
    }
}
