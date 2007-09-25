// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.pp;


import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.asmkey.logic.*;
import de.uka.ilkd.key.logic.op.NonRigidFunction;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.pp.Notation;
import de.uka.ilkd.key.pp.NotationInfo;


/** This class extends {@link de.uka.ilkd.key.pp.NotationInfo} and 
 * adds {@link de.uka.ilkd.key.pp.Notation}s
 * for ASM terms and rules.
 *
 * @author Hubert Schmid 
 * @author Stanislas Nanchen  
 */

public final class AsmNotationInfo extends NotationInfo {

    /**
     * Creates a new Operator Notation table.
     * Every Operator gets assigned its prefix, infix(es), postfix and priority.
     */
    private static Map createNotation() {
	Map map = new HashMap();
	map.put(Op.TRUE ,new Notation.Constant("TRUE",80));
	map.put(Op.FALSE,new Notation.Constant("FALSE",80));
	map.put(Op.ALL,new Notation.Quantifier("all",60,60));
	map.put(Op.EX, new Notation.Quantifier("ex", 60,60));
	map.put(AsmOperator.BOX, AsmNotation.box());
	map.put(AsmOperator.DIAMOND, AsmNotation.diamond());
	map.put(AsmProgramOperator.SEQ, AsmNotation.seq());
	map.put(AsmProgramOperator.PAR, AsmNotation.par());
	map.put(AsmProgramOperator.SKIP, AsmNotation.skip());
	map.put(AsmProgramOperator.ASSIGN, AsmNotation.assign());
	map.put(AsmProgramOperator.IF, AsmNotation.if_());
	map.put(AsmProgramOperator.ELSEIF, AsmNotation.elseif());
	map.put(AsmProgramOperator.LET, AsmNotation.let());
	map.put(AsmProgramOperator.FORALL, AsmNotation.forall());
	map.put(AsmProgramOperator.TRY, AsmNotation.try_());
	//map.put(AsmJunctor.ANDALSO, AsmNotation.andalso());
	//map.put(AsmJunctor.ORELSE, AsmNotation.orelse());
	map.put(AsmJunctor.TIMED, AsmNotation.timed());
	map.put(AsmRule.class, AsmNotation.named());
	map.put(NonRigidFunction.class, new AsmNotation.Function());
	map.put(RigidFunction.class, new AsmNotation.Function());
	map.put(NonRigidDerivedFunction.class, new AsmNotation.Function());
	map.put(RigidDerivedFunction.class, new AsmNotation.Function());
	return map;
    }
    
    
    /** Stores only the ASM notations. */
    private final Map map;
    
    
    public AsmNotationInfo() {
	map = createNotation();
    }
    
    
    public Notation getNotation(Operator op) {
	/* First check if a matching ASM notation exists. Else
	 * forward the call to the super class. */
	if (map.containsKey(op)) {
	    return (Notation) map.get(op);
	} else if (map.containsKey(op.getClass())) {
	    return (Notation) map.get(op.getClass());
	} else {
	    return super.getNotation(op, null);
	}
    }
    
    public void putAsmNotation(Operator op, Notation notation) {
	map.put(op, notation);
    }
    
}
