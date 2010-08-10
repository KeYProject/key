// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.util.keydoc.html;

import java.util.regex.*;
import java.io.File;
import java.io.FilenameFilter;


class KDFilenameFilter implements FilenameFilter {

    Pattern[] patterns;
    Matcher m;

    public KDFilenameFilter(String args[]) {

	try {
	patterns= new Pattern[args.length];
	for(int i=0; i<args.length; i++) {
	    patterns[i]= Pattern.compile(paternizeString(args[i]));
	}
	}
	catch (PatternSyntaxException pSE) {
	    System.out.println("PatternSyntaxException occured while matching your input:");
	    System.out.println(pSE.getDescription());
	    System.out.println("Erroneus Pattern: " + pSE.getPattern() + " At Index (-1 for unknown): " + pSE.getIndex());
	}
    }
    
    
    public boolean accept(File dir, String name) {
	boolean ret=false;


        for (Pattern pattern : patterns) {
            m = pattern.matcher(name);
            ret = ret || m.matches();
        }
	
	return ret;
    }

    private String paternizeString(String s) {
	String ret="";
	
	for (int i=0; i<s.length(); i++) {
       
	    if (s.charAt(i)=='*') {
		ret+= "(.*)";
	    }
	    else if (s.charAt(i)=='.') {
		ret+= "[.]";
	    }
	    else {
		ret+=(s.charAt(i));
		}
	    
	}

	return ret;
		  
    }
}


				    
