// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.proof.init.ProofInputException;

public class SLTranslationError extends java.lang.Exception {

	private String msg = "";
	
	private int line = -1;
	private int col = -1;
	
	public SLTranslationError(String msg, int line, int col) {
		this.msg = msg;
		this.line = line;
		this.col = col;
	}
	
	/**
	 * returns a message describing the problem
	 */
	public String getMessage() {
		return this.msg;
	}

	/**
	 * returns the line number within the parsed specification
	 * @return
	 */
	public int getLine() {
		return this.line;
	}
	
	/**
	 * returns the column number within the parsed specification
	 * @return
	 */
	public int getColumn() {
		return this.col;
	}
	
}
