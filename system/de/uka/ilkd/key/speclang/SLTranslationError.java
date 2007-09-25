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
