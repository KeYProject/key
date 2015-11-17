package de.uka.ilkd.key.gui.testgen;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JCheckBox;
import javax.swing.JTextField;
import javax.swing.SwingUtilities;

import de.uka.ilkd.key.gui.smt.FileChooserPanel;
import de.uka.ilkd.key.gui.smt.TablePanel;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.TestGenerationSettings;

@SuppressWarnings("serial")
class TestGenOptionsPanel extends TablePanel{
	
	private TestGenerationSettings settings;
	
	private FileChooserPanel saveToFilePanel;
	private FileChooserPanel openJMLPanel;
	private FileChooserPanel objenesisPanel;
	private JTextField maxProcesses;
	private JTextField maxUnwinds;
    private JCheckBox symbolicEx;
	private JCheckBox useJUnit;
	private JCheckBox invariantForAll;
	private JCheckBox includePostCondition;
	private JCheckBox removeDuplicates;
	private JCheckBox checkboxRFL;

	private int minWidthOfTitle;
	
	private static final String infoApplySymbolicEx = "Performs bounded symbolic execution on the current proof tree. More precisely, the TestGen Macro is executed which the user can also manually execute by right-clicking on the proof tree and selecting Strategy Macros->TestGen.";
	private static final String infoSaveTo = "Choose the folder where the test case files will be written.";
	private static final String infoMaxProcesses = "Maximal number of SMT processes that are allowed to run concurrently.";
	private static final String infoUseJunit = "Generate a JUnit 4 test suite and a test oracle from the postcondition. Disable this option when using a JML runtime checker since the generated code may be too complicated for the runtime checker or may not comply with JML requirements.";
	private static final String infoInvariantForAll = "Includes class invariants in the test data constraints. I.e., require the class invariant of all created objects to be true in the initial state.";
	private static final String infoMaxUnwinds = "Maximal number of loop unwinds or method calls on a branch that is symbolically executed when using the Strategy Macro \"TestGen\". The Strategy Macro is available by right-click on the proof tree.";
	private static final String infoRemoveDuplicates = "Generate a single testcase for two or more nodes which represent the same test data constraint. Two different nodes may represent the same test data constraint, because some formulas from the nodes which cannot be translated into a test case may be filtered out from the test data constraint.";
	private static final String infoRFLSelection = "Enables initialization of protected, private, and ghost fields with test data, " +
			                                       "as well as creation of objects from classes which have no default constructor (requires the Objenesis library)." +
			                                       "This functionality is enabled by RFL.java which is generated along the test suite. Please note, a runtime checker may not be able to handle the generated code.";
	private static final String infoOpenJMLPath = "Set location of openjml.jar. OpenJML is a third-party runtime checker. KeYTestGen generates the shell scripts compileWithOpenJML.sh and executeWithOpenJML.sh in the test output directory to simplify compilation and execution of the tests. The user should visit the OpenJML's website for additional instructions.";
	private static final String infoObjenesisPath = "Set location of objenesis.jar. Objenesis is a thrid-party library allows easy object creation from classes which do not have a (public) default constructur.";
	private static final String infoIncludePostcondition = "Includes the negated post condition in the test data constraint when generating test data. The post condition can only be included for paths (branches) where symbolic execution has finished.";
	
	public TestGenOptionsPanel(TestGenerationSettings settings){
		super();
		this.minWidthOfTitle = SwingUtilities.computeStringWidth(this.getFontMetrics(getFont()),"Concurrent ProcessesBLANK");
		this.settings = settings;
		this.setShowInfo(false);
		createTable();
	}
	
	public TestGenOptionsPanel(){		
		this(ProofIndependentSettings.DEFAULT_INSTANCE.getTestGenerationSettings());
	}
	
	@Override
    protected void createComponents() {
	   getSymbolicEx();
       getMaxUnwinds();
       getInvariantForall();
       getIncludePostCondition();
       getMaxProcesses();       
       getRFLSelectionPanel();
	   getObjenesisPanel();
	   //getRemoveDuplicatesPanel();
       getJUnitPanel();         
       getOpenJMLPanel();
       getSaveToFilePanel();
    }
	
	public JTextField getMaxProcesses() {
		if(maxProcesses == null){
			maxProcesses = addTextField("Concurrent Processes:",minWidthOfTitle,Long.toString(settings.getNumberOfProcesses()),infoMaxProcesses,
					new ActionListener(){

				@Override
				public void actionPerformed(
						ActionEvent e) {
					int value;
					try {
						value = Integer.parseInt(maxProcesses.getText());
					} catch (NumberFormatException ex) {
						value = settings.getNumberOfProcesses();
					}
					settings.setConcurrentProcesses(value);
					settings.fireSettingsChanged();
				}                                
			});
		}
		return maxProcesses;
	}
	
	public JTextField getMaxUnwinds() {
		if(maxUnwinds == null){
			maxUnwinds = addTextField("Maximal Unwinds:",minWidthOfTitle,Long.toString(settings.getMaximalUnwinds()),infoMaxUnwinds,
					new ActionListener(){

				@Override
				public void actionPerformed(
						ActionEvent e) {
					int value;
					try {
						value = Integer.parseInt(maxUnwinds.getText());
					} catch (NumberFormatException ex) {
						value = settings.getMaximalUnwinds();
					}
					settings.setMaxUnwinds(value);
					settings.fireSettingsChanged();
				}                                
			});
		}
		return maxProcesses;
	}
	
	public FileChooserPanel getSaveToFilePanel() {
		if(saveToFilePanel == null){
			saveToFilePanel = addFileChooserPanel("Store test cases to folder:",
					settings.getOutputFolderPath(), infoSaveTo, 
                        false,true,new ActionListener() {

				@Override
				public void actionPerformed(ActionEvent e) {
					settings.setOutputPath(saveToFilePanel.getPath());
					settings.fireSettingsChanged();

				}
			});
		}
		return saveToFilePanel;
	}
	public FileChooserPanel getOpenJMLPanel() {
		if(openJMLPanel == null){
			openJMLPanel = addFileChooserPanel("Location of openjml:",
					settings.getOpenjmlPath(), infoOpenJMLPath, 
                        false,true,new ActionListener() {

				@Override
				public void actionPerformed(ActionEvent e) {
					settings.setOpenjmlPath(openJMLPanel.getPath());
					settings.fireSettingsChanged();

				}
			});
		}
		return openJMLPanel;
	}
	public FileChooserPanel getObjenesisPanel() {
		if(objenesisPanel == null){
			objenesisPanel = addFileChooserPanel("Location of objenesis:",
					settings.getObjenesisPath(), infoObjenesisPath, 
                        false,true,new ActionListener() {

				@Override
				public void actionPerformed(ActionEvent e) {
					settings.setObjenesisPath(objenesisPanel.getPath());
					settings.fireSettingsChanged();

				}
			});
		}
		return objenesisPanel;
	}
	public JCheckBox getJUnitPanel(){
		if(useJUnit == null){
			
			useJUnit = addCheckBox("Generate JUnit and test oracle", infoUseJunit, settings.useJunit(), new ActionListener() {
				@Override
				public void actionPerformed(ActionEvent e) {
					settings.setUseJunit(useJUnit.isSelected());
					settings.fireSettingsChanged();
				}
			});			
		}		
		return useJUnit;		
	}
	
	public JCheckBox getRemoveDuplicatesPanel(){
		if(removeDuplicates == null){
			removeDuplicates = addCheckBox("Remove duplicates", infoRemoveDuplicates, settings.removeDuplicates(), new ActionListener() {
				@Override
				public void actionPerformed(ActionEvent e) {
					settings.setRemoveDuplicates(removeDuplicates.isSelected());
					settings.fireSettingsChanged();
				}
			});
		}
		return removeDuplicates;
	}

	public JCheckBox getRFLSelectionPanel(){
		if(checkboxRFL == null){
			checkboxRFL = addCheckBox("Use reflection framework", infoRFLSelection, settings.useRFL(), new ActionListener() {
				@Override
				public void actionPerformed(ActionEvent e) {
					settings.setRFL(checkboxRFL.isSelected());
					settings.fireSettingsChanged();
				}
			});
		}
		return checkboxRFL;
	}

    public JCheckBox getSymbolicEx(){      
        if(symbolicEx == null){            
            symbolicEx = addCheckBox("Apply symbolic execution", infoApplySymbolicEx, settings.getApplySymbolicExecution(), new ActionListener() {
                @Override
                public void actionPerformed(ActionEvent e) {
                    settings.setApplySymbolicExecution(symbolicEx.isSelected());
                    settings.fireSettingsChanged();
                }
            });         
        }       
        return symbolicEx;     
    }
	
	public JCheckBox getInvariantForall(){		
		if(invariantForAll == null){			
			invariantForAll = addCheckBox("Require invariant for all objects", infoInvariantForAll, settings.invaraiantForAll(), new ActionListener() {
				@Override
				public void actionPerformed(ActionEvent e) {
					settings.setInvariantForAll(invariantForAll.isSelected());
					settings.fireSettingsChanged();
				}
			});			
		}		
		return invariantForAll;		
	}
	
	public JCheckBox getIncludePostCondition(){		
		if(includePostCondition == null){			
			includePostCondition = addCheckBox("Include Post Condition", infoIncludePostcondition, settings.includePostCondition(), new ActionListener() {
				@Override
				public void actionPerformed(ActionEvent e) {
					settings.setIncludePostCondition(includePostCondition.isSelected());
					settings.fireSettingsChanged();
				}
			});			
		}		
		return includePostCondition;		
	}
	
	
	
	
	
}