// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui.smt;

import java.util.LinkedList;


import javax.swing.table.DefaultTableModel;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;


import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.AbstractSMTSolver;

class TemporarySolverSettings {
    public SMTSolver solver;
    public String command = "";
    public boolean isInstalled = false;
    public boolean useForMulitpleProvers = false;
    
    TemporarySolverSettings(SMTSolver solver) {
	this.solver = solver;
	newSession();
    }

    public String toString() {
	return solver.getTitle();
    }
    
    void newSession(){

	this.command = solver.getExecutionCommand();
	isInstalled = solver.isInstalled(true);
	useForMulitpleProvers = solver.useForMultipleRule();
    }

    void apply() {
	((AbstractSMTSolver) solver).setExecutionCommand(command);
	((AbstractSMTSolver) solver).useForMultipleRule(useForMulitpleProvers);
	solver.isInstalled(true);

    }

}

public class TemporarySettings extends Settings {
    
    private static TemporarySettings settingsInstance = new TemporarySettings();
    public static TemporarySettings getInstance(DecisionProcedureSettings dec, TacletTranslationSettings tac){
	settingsInstance.newSession(dec,tac);
	return settingsInstance;
    }
    
    
    private static DefaultTreeModel contentModel;
    private ContentItem defaultItem = null;
    public DecisionProcedureSettings decSettings;
    public TacletTranslationSettings tacSettings;
    public boolean showResultsAfterExecuting = false;
    public boolean storeToFile = false;
    public boolean storeTacletsToFile = false;
    public boolean cacheGoals = false;
    public int progressDialogMode=0;
    public String tacletFolder = "";
    public int maxGenerics = 3;
    public String folder = "";
    public boolean useWeakenTypeSystem = false;
    public int timeout = 10000;
    public LinkedList<TemporarySolverSettings> solverSettings = new LinkedList<TemporarySolverSettings>();
    
    public final static String    PROGRESS_MODE_USER = "Progress dialog remains open after executing solvers.";
    public final static String    PROGRESS_MODE_CLOSE ="Close progress dialog after all solvers have finished.";
    public final static String    PROGRESS_MODE_CLOSE_FIRST = "Close progress dialog after the first solver has finished.";
    
    public String getProgressMode(int index){
	switch(index){
	case DecisionProcedureSettings.PROGRESS_MODE_USER:
	    return PROGRESS_MODE_USER;
	case DecisionProcedureSettings.PROGRESS_MODE_CLOSE:
	    return PROGRESS_MODE_CLOSE;
	case DecisionProcedureSettings.PROGRESS_MODE_CLOSE_FIRST:
	    return PROGRESS_MODE_CLOSE_FIRST;
	}
	return "";
    }
    
    private TemporarySettings(){
	
    }

    private void newSession(DecisionProcedureSettings settings,
	    TacletTranslationSettings tacletSettings) {
	showResultsAfterExecuting = settings.getShowSMTResDialog();
	useWeakenTypeSystem = settings.weakenSMTTranslation;
	timeout = settings.getTimeout();
	folder = settings.getSaveToFile();
	
	if(solverSettings.isEmpty()){
	    for (SMTSolver solver : settings.getSolvers()) {
		solverSettings.add(new TemporarySolverSettings(solver));
	    }
	}else{
	    for(TemporarySolverSettings set : solverSettings){
		set.newSession();
	    }
	}


	maxGenerics = tacletSettings.getMaxGeneric();
	storeTacletsToFile = tacletSettings.isSaveToFile();
	tacletFolder = tacletSettings.getFilename();
	progressDialogMode = settings.getProgressDialogMode();
	
	storeToFile = settings.getSaveFile();
	cacheGoals = settings.isCachingGoals();

	decSettings = settings;
	tacSettings = tacletSettings;

    }



    public void applyChanges() {
	decSettings.weakenSMTTranslation = useWeakenTypeSystem;
	decSettings.setTimeout(timeout);
	decSettings.setSaveFile(storeToFile);
	decSettings.setProgressDialogMode(progressDialogMode);
	decSettings.setSaveToFile(folder);
	decSettings.setSMTResDialog(showResultsAfterExecuting);
	decSettings.setCacheGoals(cacheGoals);
	tacSettings.setFilename(tacletFolder);
	tacSettings.setMaxGeneric(maxGenerics);
	tacSettings.setSaveToFile(storeTacletsToFile);
	for (TemporarySolverSettings setSolver : solverSettings) {
	    setSolver.apply();
	}
	decSettings.fireSettingsChanged();

    }
    

	

    public DefaultTreeModel getContent() {
	if (contentModel == null) {
	   // DefaultMutableTreeNode root = new DefaultMutableTreeNode();
	    //root.setUserObject("Options");
	    DefaultTableModel def = buildModel("Options",
		    getGeneralOptionsData());
	    defaultItem = new ContentItem("Options",def );
	    DefaultMutableTreeNode root = new DefaultMutableTreeNode();
	    root.setUserObject(defaultItem);

	    DefaultMutableTreeNode solverOptions = new DefaultMutableTreeNode();
	    solverOptions.setUserObject(new ContentItem("Solvers",def ));
	    for (TemporarySolverSettings tss : solverSettings) {
		DefaultMutableTreeNode solver = new DefaultMutableTreeNode();
		solver.setUserObject(new ContentItem(tss.toString(),
		        buildModel(tss.toString(), getSolverData(tss))));
		solverOptions.add(solver);
	    }

	    DefaultMutableTreeNode tacletOptions = new DefaultMutableTreeNode();
	    tacletOptions.setUserObject(new ContentItem("Taclets",
		    buildModel("Taclets", getTacletOptionsData())));

	    DefaultMutableTreeNode tacletSelection = new DefaultMutableTreeNode();
	    tacletSelection.setUserObject(new ContentItem("Selection",
		    TacletTranslationSelection.INSTANCE
		            .getSelectionTree()));
	    tacletOptions.add(tacletSelection);
	

	   
	    root.add(solverOptions);
	    root.add(tacletOptions);

	    contentModel = new DefaultTreeModel(root);
	    // setModel(model);

	} else {
	    // init((DefaultMutableTreeNode)contentModel.getRoot());
	}
	return contentModel;

    }
    
    

    private TableComponent[] getSolverData(TemporarySolverSettings tss) {
	TableComponent data[] = {
	        new TableProperty(tss){

		
                    public boolean prepareValues() {
			 this.setTitle("Name:");
			 this.setValue(((TemporarySolverSettings)this.getUserObject())
				 .solver.getTitle());
			 this.setEditable(false);
	                 return true;
                    }

		    public void eventChange() {}
	            
	        },
	        new TableProperty(tss){

	
                    public boolean prepareValues() {
			 this.setTitle("Installed:");			 
			 this.setValue(((TemporarySolverSettings)this.getUserObject())
				 .solver.isInstalled(true));
			 this.setEditable(false);
			 
	                return true;
                    }

		    public void eventChange() {}
		    public String getInfo(){
			return "There are two ways to make supported provers applicable for KeY:\n" +
				"1. Specify the absolute path of the prover in the field below.\n"+
				"2. Change the enviroment variable $PATH of your system, so that it " +
				"refers to the installed prover.";
		    }
	            
	        },
	        
	        
	        
	        new TableProperty(tss) {
		
                   public boolean prepareValues() {
			 this.setTitle("Command:");
			 this.setValue(((TemporarySolverSettings)this.getUserObject())
				 .command);
			 this.setEditable(true);
	                return true;
                    }

		    public void eventChange() {
		        ((TemporarySolverSettings) getUserObject()).command = getValue();
		    }	
		    
	
		        @Override
		        public String getInfo() {
		           return "Editing the start command:\n" +
				"Specify the start command for an external procedure in such a way that it can be executed " +
				"to solve a problem file. Feel free to use any parameter to finetune the program.\n\n" +
				"Use %f as placeholder for the filename containing the problemdescription.\n\n" +
				"Use %p as placeholder for the problem directly. This should be needed in special cases only.";
		        }
	        },

	        new TableCheckBox(tss) {
		    @Override
		    public void eventChange() {
		        ((TemporarySolverSettings) getUserObject()).useForMulitpleProvers = isSelected();
		    }

	
                    public boolean prepareValues() {
		        setTitle("Use this prover for the rule 'multiple provers'.");
		        setSelected(((TemporarySolverSettings) getUserObject()).useForMulitpleProvers);
	                return true;
                    }

                    public String getInfo(){
                	return "All provers for which this option is activated" +
                		" are executed concurrently when the rule 'multiple provers'"+
                		" is applied.\n\n"+
                		"This option must be activated for at least two provers to"+
                		" enable the rule"+
                		" 'multiple provers'.";
                    }
	
	        },
	
	        
	        new TableExplanation(tss,"Information"){
	            public boolean visible() {
	        	SMTSolver solver =  ((TemporarySolverSettings) getUserObject())
	        	.solver;
	        	String info = solver.getInfo();
	        	return info !=  null && !info.isEmpty();
	            };
	            public boolean prepareValues() {
	        	super.prepareValues();
	        	SMTSolver solver =  ((TemporarySolverSettings) getUserObject())
	        	.solver;
	        	String info = solver.getInfo();
	        	
	        	if(info ==  null || info.isEmpty()){
	        	    // Don't show the component if there is no information
	        	    // to present.
	        	    return false;
	        	}
	        	init(info);
	        	return true;
	            };
	        }

	};
	return data;
    }

    private TableComponent[] getGeneralOptionsData() {
	TableComponent data[] = {



	new TableCheckBox() {
	    public boolean prepareValues() {
		setTitle("Show results in a dialog after executing the solvers.");
		setSelected(showResultsAfterExecuting);
		return true;
	    }

	    @Override
	    public void eventChange() {
		showResultsAfterExecuting = isSelected();
	    }
	    
	    @Override
	    public String getInfo() {
		return "If you activate this option, a dialog " +
		"will pop up showing results after executing the solvers.\n"+
		"This dialog may help you to relate the results to the corresponding\n" +
		"goals.";
	    }
	},

	new TableCheckBox() {

	    @Override
	    public void eventChange() {
		useWeakenTypeSystem = isSelected();

	    }

	    public boolean prepareValues() {
		setTitle("Use translation of weaken type system.");
		setSelected(useWeakenTypeSystem);
		return true;
	    }
	    @Override
	    public String getInfo() {
		return "When activated, the axiomatization of KeY's type system " +
		"is weakend during export to the SMT format. In particular "+
		"axioms with quantifiers are removed or instantiated. " +
		"This does not destroy soundness for verification, however, " +
		"counter examples generated by SMT solvers may not fully satisfy " +
		"the type system.";
	    }

	}/*,	new TableCheckBox() {

	    public boolean prepareValues() {
		setTitle("Cache goals.");
		setSelected(cacheGoals);
		return true;
	    }

	    @Override
	    public void eventChange() {
		cacheGoals = isSelected();

	    }
	    public String getInfo() 
	    {return "If this option is selected, goals are cached.\n"+
		      "(Not yet implemented)";}
	    
	
	
	}*/





	,

	new TableSaveToFile() {

	    public boolean prepareValues() {
		setTitle("Store translation to file:");
		setFolder(folder);
		setActivated(storeToFile);
		//enable(storeToFile);
		return true;
	    }

	    public void eventChange() {
		folder = getFolder();
		storeToFile = isActivated();
		//enable(isActivated());

	    }
	    

	    @Override
	    public String getInfo() {
		return "Activate this option to store the translations " +
			"that are handed over to the externals solvers:\n" +
			"1. Choose the folder.\n"+
			"2. Specify the filename:\n"+
				"\t%s: the solver's name\n"+
				"\t%d: date\n"+
				"\t%t: time\n"+
				"\t%i: the goal's number\n"+
			"\n\n"+
			"Example: /home/translations/%d_%t_%i_%s.txt"+"\n\n"+
			"Remark: After every restart of KeY this option "+
			"is deactivated.";
	    }

	}
	
	,
	
	
	
	
	 new TableComboBox(progressDialogMode,getProgressMode(DecisionProcedureSettings.PROGRESS_MODE_USER),
	         getProgressMode(DecisionProcedureSettings.PROGRESS_MODE_CLOSE),
	         getProgressMode(DecisionProcedureSettings.PROGRESS_MODE_CLOSE_FIRST)) {

	    public void eventChange() {
		progressDialogMode = getSelectedItemIndex();
	    }

	    public boolean prepareValues() {
		setSelectedItem(progressDialogMode);
		return true;
	    }
	    
	    public String getInfo(){
		return "1. Option: The progress dialog remains open " +
			"after executing the solvers so that the user " +
			"can decide whether he wants to accept the results.\n" +
			"\n" +
			"2. Option: The progress dialog is closed once the " +
			"external provers have done their work or the time limit " +
			"has been exceeded.\n"+
			"\n"+
			"3. Option: The progress dialog is closed once the first " +
			"external prover has successfully solved all given goals " +
			"or the time limit has been exceeded.";
	    }
      
	},

	new TableProperty(this) {

	    public void eventChange() {
	        int value;
	        try {
		    float val = Float.parseFloat(getValue());
		    value = (int)(val*10);
	        } catch (NumberFormatException e) {
		    value = timeout;
	        }
	        timeout = value;
	        
	        

	    }
	
            public boolean prepareValues() {
		setTitle("Timeout:");
		setValue(((float)timeout/10));
	        return true;
            }
            
            public String getInfo() {
        	return "Timeout for the external solvers in seconds. Fractions of a second are allowed.\n" +
        		"Example: 6.5";
            };


	}

	};

	return data;

    }

    private TableComponent[] getTacletOptionsData() {
	TableComponent data[] = {

	        new TableSaveToFile() {

		    public boolean prepareValues() {
		        setFolder(tacletFolder);
		        setActivated(storeTacletsToFile);
		        //enable(storeTacletsToFile);
		        setTitle("Store taclet translation to file:");
		        return true;
		    }

		    public void eventChange() {
		        tacletFolder = getFolder();
		        storeTacletsToFile = isActivated();
		       // enable(isActivated());

		    }
		    
		    @Override
		    public String getInfo() {
			return "Activate this option to store the translations of taclets" +
				" that are handed over to the externals solvers:\n" +
				"1. Choose the folder.\n"+
				"2. Specify the filename:\n"+
					"\t%s: the solver's name\n"+
					"\t%d: date\n"+
					"\t%t: time\n"+
					"\t%i: the goal's number\n"+
				"\n\n"+
				"Example: ./home/translations/Taclet%d_%t_%i_%s.txt"+"\n\n"+
				"Note: After every restart of KeY this option"+
				" is deactivated.";
		    }
	        },
	        new TableProperty(this) {
		    public void eventChange() {
		        int value;
		        try {
			    value = Integer.parseInt(getValue());
		        } catch (NumberFormatException e) {
			    value = maxGenerics;
		        }
		        maxGenerics = value;
		    }

		    public boolean prepareValues() {
			setTitle("Maximum number of different generic sorts:");
		        setValue(maxGenerics);
		        return true;
		    };
		    
		    public String getInfo(){
			return "This option specifies how many different generic sorts are allowed"+
			 " within a taclet.\n\n"+
			 "Be aware of the fact that too many different generic sorts can" +
			 " overwhelm the external solvers. On the other side there are taclets that" +
			 " use a certain amount of different generic sorts (see: taclet selection).\n\n"+
			 "Rule of thumb: Most of the taclets can be translated by using 2-3 different" +
			 " generic sorts.";
		    }

	        }

	};

	return data;

    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.smt.Settings#getDefaultItem()
     */
    @Override
    public ContentItem getDefaultItem() {
	return defaultItem;
    }

}
