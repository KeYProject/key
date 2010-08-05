package de.uka.ilkd.key.smt.launcher;
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                  Universitaet Koblenz-Landau, Germany
//                  Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//


public interface ProcessListener {
	void eventException(Process p , Exception e);
	void eventInterruption(Process p);
	void eventFinished(Process p);
	void eventStarted(Process p);
        void eventCycleFinished(Process process, Object userObject);
	
}
