// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.SetOfRuleApp;

public interface ProofCorrectnessMgt {

    boolean contractApplicableFor(ProgramMethod pm, Goal g);

    ProofStatus getStatus();

    void updateProofStatus();
    
    void ruleApplied(RuleApp r);

    void ruleUnApplied(RuleApp r);
    
    SetOfRuleApp getNonAxiomApps();

    void setMediator ( KeYMediator p_mediator );

    boolean proofSimilarTo(Proof p);

    RuleJustification getJustification(RuleApp app);
    
    void removeProofListener();
}
