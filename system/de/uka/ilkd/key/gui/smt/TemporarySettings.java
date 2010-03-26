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

import java.util.LinkedList;

import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.AbstractSMTSolver;


class TemporarySolverSettings{
    public SMTSolver solver;
    public String command = "";
    public boolean useForMulitpleProvers = false;
    
    public TemporarySolverSettings(SMTSolver solver) {
	this.solver = solver;
	this.command = solver.getExecutionCommand();
	useForMulitpleProvers = solver.useForMultipleRule();
    }
    
    public String toString(){
	return solver.getTitle();
    }
    
    public void apply(){
	((AbstractSMTSolver) solver).setExecutionCommand(command);
	((AbstractSMTSolver) solver).useForMultipleRule(useForMulitpleProvers);
	
    }
   
    
    
}

public class TemporarySettings {
    
    public boolean showResultsAfterExecuting = false;
    public boolean storeToFile               = false;
    public boolean storeTacletsToFile 	       = false;
    public boolean cacheGoals		       = false;
    public String   progressDialogMode;
    public String   tacletFolder	       = "";
    public int     maxGenerics		       = 3;
    public String   folder		       = "";
    public boolean useWeakenTypeSystem       = false;
    public int     timeout 		       = 10000;
    public LinkedList<TemporarySolverSettings> solverSettings 
            = new LinkedList<TemporarySolverSettings>();
    
    
    TemporarySettings(DecisionProcedureSettings settings, TacletTranslationSettings tacletSettings){
	showResultsAfterExecuting = settings.getShowSMTResDialog();
	useWeakenTypeSystem       = settings.weakenSMTTranslation;
	timeout 		  = settings.getTimeout();
	folder			  = settings.getSaveToFile();
	for(SMTSolver solver : settings.getSolvers()){
	    solverSettings.add(new TemporarySolverSettings(solver));
	}
	
	maxGenerics = tacletSettings.getMaxGeneric();
	storeTacletsToFile = tacletSettings.isSaveToFile();
	tacletFolder       = tacletSettings.getFilename();
	progressDialogMode = settings.getProgressDialogMode();
	storeToFile        = settings.getSaveFile();
	cacheGoals 	   = settings.isCachingGoals();

	
	
	
    }
    
    void apply(DecisionProcedureSettings settings, TacletTranslationSettings tacletSettings){
	settings.weakenSMTTranslation = useWeakenTypeSystem;
	settings.setTimeout(timeout);
	settings.setSaveFile(storeToFile);
	settings.setProgressDialogMode(progressDialogMode);
	settings.setSaveToFile(folder);
	settings.setSMTResDialog(showResultsAfterExecuting);
	settings.setCacheGoals(cacheGoals);
	tacletSettings.setFilename(tacletFolder);
	tacletSettings.setMaxGeneric(maxGenerics);
	tacletSettings.setSaveToFile(storeTacletsToFile);
	for(TemporarySolverSettings setSolver : solverSettings){
	    setSolver.apply();
	}
	
	
    }
    
    
    
  
    

}
