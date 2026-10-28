/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.informationflow.po;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.informationflow.ProofObligationVars;
import de.uka.ilkd.key.informationflow.proof.init.StateVars;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 * This class contains the set of four sets of ProofObligationVars necessary for information flow
 * proofs.
 *
 * @author christoph
 *
 */
@NullMarked
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
        linkSymbExecVarsToCopies(infFlowToSymbExecVarsMaps, symbExecVars);
    }


    public IFProofObligationVars labelHeapAtPreAsAnonHeapFunc() {
        ProofObligationVars newC1 = c1.labelHeapAtPreAsAnonHeapFunc();
        ProofObligationVars newC2 = c2.labelHeapAtPreAsAnonHeapFunc();
        ProofObligationVars sev = symbExecVars.labelHeapAtPreAsAnonHeapFunc();
        return new IFProofObligationVars(newC1, newC2, sev);
    }


    private static void linkSymbExecVarsToCopies(
            Map<ProofObligationVars, Map<JTerm, JTerm>> infFlowToSymbExecVarsMaps,
            ProofObligationVars symbExecVars) {
        for (ProofObligationVars ifVars : infFlowToSymbExecVarsMaps.keySet()) {
            final Map<JTerm, JTerm> map = infFlowToSymbExecVarsMaps.get(ifVars);
            if (map == null) {
                throw new NullPointerException(
                    "No variable map for the information flow variables " + ifVars + ".");
            }
            linkStateVarsToCopies(ifVars.pre, symbExecVars.pre, map);
            linkStateVarsToCopies(ifVars.post, symbExecVars.post, map);
        }
    }


    private static void linkStateVarsToCopies(StateVars ifVars, StateVars seVars,
            Map<JTerm, JTerm> map) {
        final Iterator<JTerm> ifVarsIt = ifVars.termList.iterator();
        for (final JTerm symbTerm : seVars.termList) {
            final JTerm ifTerm;
            if (ifVarsIt.hasNext()) {
                ifTerm = ifVarsIt.next();
            } else {
                ifTerm = null;
            }
            if (symbTerm != null) {
                linkToCopy(map, symbTerm, ifTerm);
            }
        }
    }


    /**
     * Links a symbolic execution term to its counterpart in an information flow
     * copy.
     *
     * <p>
     * The counterpart may be absent ({@code null}): some proof configurations
     * carry a shorter term list in the copy than in the symbolic execution
     * variables (for instance when the measured-by variable is present only in
     * the symbolic execution copy). This is deliberate and historically
     * recorded as a key mapped to {@code null}: the consumer
     * {@code InfFlowProgVarRenamer} decides via {@code containsKey} whether a
     * term has a counterpart, and a present key mapped to {@code null} is
     * observably different from an absent key there. The map's value type
     * cannot be widened to {@code @Nullable} because the downstream consumers
     * in key.core declare the unannotated {@code Map<JTerm, JTerm>}.
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    private static void linkToCopy(Map<JTerm, JTerm> map, JTerm symbTerm,
            @Nullable JTerm ifTerm) {
        map.put(symbTerm, ifTerm);
    }


    public @Nullable Map<JTerm, JTerm> getMapFor(ProofObligationVars vars) {
        return infFlowToSymbExecVarsMaps.get(vars);
    }


    @Override
    public String toString() {
        return "[" + symbExecVars + "," + c1 + "," + c2 + "]";
    }
}
