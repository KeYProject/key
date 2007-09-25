// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.rule.soundness;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.SourceData;
import de.uka.ilkd.key.java.abstraction.ArrayOfKeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.rule.MatchConditions;



public class ProgramSVSkolemStatement extends ProgramSVSkolem {

    public ProgramSVSkolemStatement ( ProgramElementName p_name,
				      ArrayOfKeYJavaType p_influencingPVTypes,
				      int                p_jumpCnt ) {
	super ( p_name, p_influencingPVTypes, p_jumpCnt );
    }

    public PositionInfo getPositionInfo () {
        return PositionInfo.UNDEFINED;
    }

 
    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        // TODO Auto-generated method stub
        return null;
    }
}
