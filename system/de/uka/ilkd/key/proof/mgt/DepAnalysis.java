// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Rule;

public class DepAnalysis {

    private final boolean depExists;
    private final Rule r;
    private final Proof p;
    private final String info;

    private static final DepAnalysis noDepInstance 
	= new DepAnalysis(false, "No Dependency");

    public static DepAnalysis getInstance(boolean depExists, Rule r, 
					  Proof p, String info) {
	if (!depExists) {
	    return noDepInstance;
	} else {
	    return new DepAnalysis(depExists, r, p, info);
	}
    }

    public static DepAnalysis getInstance(boolean depExists, Rule r, 
					  Proof p) {
	return getInstance(depExists, r, p, "");
    }

    public static DepAnalysis getInstance(boolean depExists, String info) {
	return getInstance(depExists, null, null, info);
    }


    private DepAnalysis(boolean depExists, Rule r, Proof p, String info) {
	this.depExists=depExists;
	this.r=r;
	this.p=p;
	this.info=info;
    }

    public DepAnalysis(boolean depExists, String info) {
	this(depExists, null, null, info);
    }

    public String toString() {
	StringBuffer res = null;
	if (r!=null && p!=null) {
	    res = new StringBuffer("Rule "+r.name()+" is ");
	    if (depExists) res.append("not ");
	    res.append("used in proof "+p.name()+". ");
	}
	return (res!=null) ? res+info : info;
    }

    public boolean depExists() {
	return depExists;
    }

}
