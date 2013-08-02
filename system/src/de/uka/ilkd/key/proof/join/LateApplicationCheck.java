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

package de.uka.ilkd.key.proof.join;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.delayedcut.ApplicationCheck;

public enum LateApplicationCheck {
	INSTANCE;
	public List<String> check(Node node, Node cutNode, ApplicationCheck check){
		return check(check,node.sequent(),cutNode);
		
	}
	
	private List<String> check(ApplicationCheck check, Sequent sequent, Node cutNode){
		List<String> conflicts = new LinkedList<String>();
		for(Iterator<SequentFormula> it =  sequent.iterator(); it.hasNext();){
			SequentFormula sf = it.next();
			String result = check.check(cutNode, sf.formula());
			if(result != null){
				conflicts.add(result);
			}
		}
		return conflicts;
	}
}