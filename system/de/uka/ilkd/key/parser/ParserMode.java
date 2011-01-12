// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.parser;

public class ParserMode {
    public static final ParserMode DECLARATION = new ParserMode();
    public static final ParserMode TERM = new ParserMode();
    public static final ParserMode GLOBALDECL = new ParserMode();
    public static final ParserMode TACLET = new ParserMode();
    public static final ParserMode PROBLEM = new ParserMode();  
    public String getName() {
	if(this == DECLARATION)
	   return "DECLARATION";
	if(this == TERM)
	   return "TERM";
	if(this == GLOBALDECL)
	   return "GLOBALDECL";
	if(this == TACLET)
	   return "TACLET";
	if(this == PROBLEM)
	   return "PROBLEM";
	return "UNKNOWN";
    }
}
