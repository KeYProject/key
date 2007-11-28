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

import java.util.Iterator;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;

public interface ProofCorrectnessMgt {

    boolean ruleApplicable(RuleApp r, Goal g);

    String getLastAnalysisInfo();

    ProofStatus getStatus();

    void updateProofStatus();
    
    void ruleApplied(RuleApp r);

    void ruleUnApplied(RuleApp r);
    
    Iterator getAppliedNonAxioms();

    void setMediator ( KeYMediator p_mediator );

    boolean proofSimilarTo(Proof p);

    RuleJustification getJustification(RuleApp app);

}
