// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.pp;

public class AbbrevException extends Exception{
	
	/**
     * 
     */
    private static final long serialVersionUID = 7602628448672131434L;
    protected boolean termused;

	public AbbrevException(String message,boolean termused){
		super(message);
		this.termused = termused;
	}
}