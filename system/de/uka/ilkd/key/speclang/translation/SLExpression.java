// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Debug;


/**
 *  This class represents an expression of an arbitrary specification language.
 *  We assume that every expression is either a Term, Type or a Collection.
 */
public abstract class SLExpression {

    private final Term term;
    private final KeYJavaType type;
    private final SLCollection collection;


    public SLExpression(Term term) {
	Debug.assertTrue(term != null);
	this.term = term;
	this.type = null;
	this.collection = null;
    }


    public SLExpression(KeYJavaType type) {
	Debug.assertTrue(type != null);
	this.term = null;
	this.type = type;
	this.collection = null;
    }


    public SLExpression(SLCollection c) {
	Debug.assertTrue(c != null);
	this.term = null;
	this.type = null;
	this.collection = c;
    }


    public boolean isTerm() {
	return this.term != null;
    }


    public boolean isType() {
	return this.type != null;
    }


    public boolean isCollection() {
	return this.collection != null;
    }


    public Term getTerm() {
	return this.term;
    }


    public KeYJavaType getType() {
	return this.type;
    }


    public SLCollection getCollection() {
	return this.collection;
    }


    public KeYJavaType getKeYJavaType(JavaInfo javaInfo) {
	if (this.isTerm()) {
	    if (this.getTerm().sort() != Sort.FORMULA) {
		return javaInfo.getServices().getTypeConverter()
			.getKeYJavaType(this.getTerm());
	    } else {
		return javaInfo.getServices().getTypeConverter()
			.getBooleanType();
	    }
	} else if (this.isType()) {
	    return this.getType();
	} else {
	    // receiver is a collection
	    return javaInfo.getKeYJavaType(this.getCollection()
		    .getElementSort());
	}
    }


    public String toString() {
	if (isTerm()) {
	    return term.toString();
	} else if (isType()) {
	    return type.toString();
	} else {
	    return collection.toString();
	}
    }


    public Sort getSort() {
	if (this.isTerm()) {
	    return this.getTerm().sort();
	} else if (this.isType()) {
	    return this.getType().getSort();
	} else {
	    // receiver is a collection
	    return this.getCollection().getElementSort();
	}
    }
}
