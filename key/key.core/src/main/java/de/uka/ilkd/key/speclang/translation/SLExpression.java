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

package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;


/**
 *  This class represents the translation of an expression of an arbitrary
 *  specification language, which in the KeY world is either a term or a type.
 */
public final class SLExpression {

    private final Term term;
    private final KeYJavaType type;
    private final boolean isTerm;


    public SLExpression(Term term,
	                KeYJavaType type,
	                boolean isTerm) {
	assert term != null;
	assert type != null;
	assert term.sort() == type.getSort()
	       : "term has sort: " + term.sort()
	         + "; type has sort: " + type.getSort();
	this.term = term;
	this.type = type;
	this.isTerm = isTerm;
    }


    public SLExpression(Term term,
	                KeYJavaType type) {
	this(term, type, true);
    }


    /**
     * USE WITH CARE! Term-SLExpressions should have a type!
     */
    public SLExpression(Term term) {
	assert term != null;
	this.term = term;
	this.type = null;
	this.isTerm = true;
    }


    public SLExpression(KeYJavaType type) {
	assert type != null;
	this.term = null;
	this.type = type;
	this.isTerm = false;
    }


    public boolean isTerm() {
	return isTerm;
    }


    public boolean isType() {
	return !isTerm;
    }


    public Term getTerm() {
	return term;
    }


    public KeYJavaType getType() {
	return type;
    }


    @Override
    public String toString() {
	if(isTerm()) {
	    return term + "(type: " + type + ")";
	} else {
	    return type.toString();
	}
    }
}