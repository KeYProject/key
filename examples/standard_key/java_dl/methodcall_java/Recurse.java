// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
public class Recurse {

    int recurse(boolean clear) {
	int x = 1;
	if ( clear ) {
	    x=0;
	} else {
	    recurse(true);
	}
	return x;
    }

}
