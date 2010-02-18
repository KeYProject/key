// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.visualization;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.proof.Node;

/** This trace element can represent a modality (or program) on which
 * symbolic execution didn't take place yet. This is useful for constructing
 * traces for black-box testing.
 * @author gladisch*/
public class UnexecutedTraceElement extends TraceElement {
    /**Determins whether the traced modality is in the antecdent. This is usually
     * determined from posOfModality, but if no symbolic execution takes
     * place posOfModality may be null.*/
    private Boolean inAntec=null;
    
    /** This trace element can represent a modality (or program) on which
     * symbolic execution didn't take place yet. This is useful for constructing
     * traces for black-box testing.
     * @author gladisch*/
    public UnexecutedTraceElement(SourceElement prElement, ProgramElement program, Boolean inAntec, Node n,  TraceElement nip, ContextTraceElement ne, IExecutionContext exCont){
        node = n;
        /*To set posOfModality = n.getAppliedRuleApp().posInOccurrence(); is wrong, because
          UnexecutedTraceElement is usually created from a modal operator that is not
          symbolically executed. Thus n.getAppliedRuleApp().posInOccurrence() must refere to a different
          modal operator or formula with a modal operator than the modal operator represented
          by this UnexecutedTraceElement. */
        posOfModality = null;
        //assert inAntec!=null; This is required by UnitTestBuilder
        this.inAntec = inAntec;
        nextInProof = nip;
        stepInto = ne;
        programElement = prElement;
        executionContext = exCont;
        this.program = program;
    }

/**To determine the position of the modality from n.getAppliedRuleApp().posInOccurrence() is wrong
  because UnexecutedTraceElement is usually created from a modal operator that is not
  symbolically executed. Thus n.getAppliedRuleApp().posInOccurrence() must refere to a different
  modal operator or formula with a modal operator than the modal operator represented
  by this UnexecutedTraceElement. Therefore 
   n.getAppliedRuleApp().posInOccurrence().isInAntec may differ from inAntec
   */
    public Boolean isInAntec(){
            return inAntec;
    }

}
