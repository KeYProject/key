// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

/**
 * 
 */
package de.uka.ilkd.key.logic;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.sort.Sort;

/**
 * @author mihai
 *
 */
public class SortCollector extends DefaultVisitor {	
	
	private Set<Sort> sorts;	

	public SortCollector() {
		sorts = new HashSet<Sort>();
	}
	
	public Set<Sort> getSorts() {
		return sorts;
	}	
	
	/* (non-Javadoc)
	 * @see de.uka.ilkd.key.logic.DefaultVisitor#visit(de.uka.ilkd.key.logic.Term)
	 */
	@Override
	public void visit(Term visited) {
		sorts.add(visited.sort());
	}	

}