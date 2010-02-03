// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java;

public class PosConvertException extends ConvertException {

    int line;
    int col;
    
    public PosConvertException(String m, int l, int c) {
	super(m);
	line=l;
	col=c;
    }

    
    public int getLine() {
	return line;
    }

    public int getColumn() {
	return col;
    }
    
}
