// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.NonInterferencePO;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;

public class NonInterferenceCheck {

    private Proof proof1, proof2;

    public NonInterferenceCheck(BasicTask[] tasks) {
        if (tasks.length != 2) throw new IllegalStateException(
            "Non-Interference checker needs 2 proofs, got "+tasks.length);
        proof1 = tasks[0].proof();
        proof2 = tasks[1].proof();
        // XXX: test if proofs in same env.
    }
    
    public void run() {
        ProofEnvironment env = proof1.env();
        NonInterferencePO nipo = new NonInterferencePO(env,proof1,proof2);
        ProblemInitializer pi = new ProblemInitializer(Main.getInstance());
        try {
            pi.startProver(env, nipo);
        } catch(ProofInputException e) {
            System.err.println(e.toString());
        }
        nipo.createSubgoals();
    }

}
