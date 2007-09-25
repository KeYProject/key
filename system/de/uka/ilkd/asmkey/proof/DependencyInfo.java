// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.proof;

import de.uka.ilkd.asmkey.parser.ast.AstProof;
import de.uka.ilkd.asmkey.unit.Unit;
import de.uka.ilkd.asmkey.unit.UnitManager;
import de.uka.ilkd.key.logic.ListOfNamed;
import de.uka.ilkd.key.logic.SLListOfNamed;

/**
 * This class is a intermediary, used to transfer knowledge
 * from the {@link AstProof} in the {@link UnitManager} without
 * replaying the proof and before adding the info into the key proof
 * mgt system and into the prop/taclet dependancy graph of {@link Unit}.
 *
 * @author Stanislas Nanchen
 */
public class DependencyInfo {

    public static final int AXIOM = 0;
    public static final int LEMMA = 1;
    public static final int MATHEMATICAL_TRUTH = 2;
    public static final int UNKNOWN = 3;
    public static final int ERROR = -1;

    private ListOfNamed usedProps;
    private int type;

    public DependencyInfo() {
	this(UNKNOWN, SLListOfNamed.EMPTY_LIST);
    }

    public DependencyInfo(int type, ListOfNamed usedProps) {
	this.type = type;
	this.usedProps = usedProps;
    }

    public int type() {
	return type;
    }

    public void setType(int type) {
	this.type = type;
    }

    public ListOfNamed usedPropositions() {
	return usedProps;
    }
    
    public void setUsedPropositions(ListOfNamed usedProps) {
	this.usedProps = usedProps;
    }

}
