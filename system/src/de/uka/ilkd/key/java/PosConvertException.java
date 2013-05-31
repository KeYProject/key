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

package de.uka.ilkd.key.java;

public class PosConvertException extends ConvertException {

    /**
     * 
     */
    private static final long serialVersionUID = 758453353495075586L;
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
