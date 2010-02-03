// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.pp;

public class AbbrevException extends Exception{
	
	protected boolean termused;

	public AbbrevException(String message,boolean termused){
		super(message);
		this.termused = termused;
	}

	/**
	 * returns true if the cause of the Exception was that the term is already 
	 * mapped to a abbreviation. If false is returned the abbreviation is in use for
	 * another term.
	 */ 
	public boolean TermUsed(){
		return termused;
	}

} 
