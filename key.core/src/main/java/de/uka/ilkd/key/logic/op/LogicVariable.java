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

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * The objects of this class represent logical variables,
 * used e.g. for quantification.
 */
public final class LogicVariable extends AbstractSortedOperator 
    implements QuantifiableVariable, ParsableVariable {

    public LogicVariable(Name name, Sort sort) {
	super(name, sort, true);
	assert sort != Sort.FORMULA;
	assert sort != Sort.UPDATE;
    }
    
    
    @Override
    public String toString() {
	return name() + ":" + sort();
    }
}