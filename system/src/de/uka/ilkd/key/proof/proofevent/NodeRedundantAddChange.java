// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.proof.proofevent;

import de.uka.ilkd.key.logic.PosInOccurrence;

/** 
 * An instance of this class informs the listerns if a formula has been
 * tried to add to the sequent 
 */
public class NodeRedundantAddChange implements NodeChange {

    /** the PosInOccurrence of the formula that has been tried to add */
    private final PosInOccurrence pio;
    
    /**
     *  creates an instance 
     *  @param pio the PosInOccurrence of the formula that has been tried to add
     */
    public NodeRedundantAddChange(PosInOccurrence pio) {
        this.pio = pio;
    }         

    /**
     * returns the PosInOccurrence of the formula that has been tried to add
     * @return the PosInOccurrrence 
     */
    public PosInOccurrence getPos() {
        return pio;
    }
    
    /** toString */
    public String toString() {
        return "Redundant formula:" + pio;
    }
    
}
