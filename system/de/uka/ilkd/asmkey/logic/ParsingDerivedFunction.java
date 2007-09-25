// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.logic;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.Location;

/**
 * this class is used during the parsing,
 * to allow the build up step by step of
 * the derived functions:
 * 1. collection of symbol
 * 2. parsing of bodies
 * 3. nonrigid info, recursive info and other infos.
 */
public class ParsingDerivedFunction extends DerivedFunction {

    private boolean isRigid;
    private Location location;

    public ParsingDerivedFunction(Name name, Sort sort, FormalParameter[] args,
				  Location location) {
	this(name, sort, args, null, location);
    }

    public ParsingDerivedFunction(Name name, Sort sort, FormalParameter[] args, AsmTerm term,
				  Location location) {
	/* at the beginning, everything is not recursive */
	super(name, sort, args, term, false);
	/* at the beginning, everything is "rigid". */
	this.isRigid = true;
	this.location = location;
    }

    

    public void setRecursiveFlag(boolean isRec) {
	this.isRec = isRec;
    }
    
    public boolean isRigid() {
	return isRigid;
    }

    public boolean isRigid(Term term) {
	return isRigid();
    }

    public void setNonRigid() {
	isRigid = false;
    }
    
    public Location location() {
	return location;
    }

}
