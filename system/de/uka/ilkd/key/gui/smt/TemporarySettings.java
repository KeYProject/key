// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui.smt;


class TemporarySolverSettings{
    public String command = "";
    
    
}

public class TemporarySettings {
    
    public boolean showResultsAfterExecuting = false;
    public boolean storeToFile               = false;
    public String   folder		       = "";
    public boolean useWeakenTypeSystem       = false;
    public int     timeout 		       = 10000;
    
    TemporarySettings(DecisionProcedureSettings settings){
	showResultsAfterExecuting = settings.getShowSMTResDialog();
	useWeakenTypeSystem       = settings.weakenSMTTranslation;
	timeout 		  = settings.getTimeout();
	
    }

}
