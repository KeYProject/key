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


package de.uka.ilkd.key.pp;


/**
 * A class specifying a range of integer numbers e.g. character positions.
 */

public class Range {
    int start = -1;
    int end = -1;
    
    public Range(int s, int e){
	start = s;
	end = e;
    }

    public Range(Range r) {
	start = r.start;
	end   = r.end;
    }
    
    public int start(){
	return start;
    }
    
    public int end(){
	return end;
    }

    public int length() {
	return end-start;
    }

    public String toString(){
	return "[ Start = " + start + " ; End = " + end + " ]";
    }
} 
