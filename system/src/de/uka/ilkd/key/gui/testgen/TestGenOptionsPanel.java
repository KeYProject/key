package de.uka.ilkd.key.gui.testgen;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JCheckBox;
import javax.swing.JTextField;
import javax.swing.SwingUtilities;

import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.gui.smt.FileChooserPanel;
import de.uka.ilkd.key.gui.smt.TablePanel;

@SuppressWarnings("serial")
class TestGenOptionsPanel extends TablePanel{
	
	private TestGenerationSettings settings;
	
	private FileChooserPanel saveToFilePanel;
	private JTextField maxProcesses;
	private JTextField maxUnwinds;
	private JCheckBox useJUnit;
	private JCheckBox invariantForAll;
	private JCheckBox removeDuplicates;

	private int minWidthOfTitle;
	
	private static final String infoSaveTo = "Choose the folder where the testcase files will be written.";
	private static final String infoMaxProcesses = "Maximal number of SMT processes that are allowed to run concurrently.";
	private static final String infoUseJunit = "Generate JUnit test suites (Test oracles not yet implemented).";
	private static final String infoInvariantForAll = "Require the invariant of all created objects to be true.";
	private static final String infoMaxUnwinds = "Maximal number of loop unwinds or method calls on a branch.";
	private static final String infoRemoveDuplicates = "Generate a single testcase for two ore more identical nodes.";
	
	public TestGenOptionsPanel(TestGenerationSettings settings){
		super();
		this.minWidthOfTitle = SwingUtilities.computeStringWidth(this.getFontMetrics(getFont()),"Concurrent ProcessesBLANK");
		this.settings = settings;
		createTable();
	}
	
	public TestGenOptionsPanel(){		
		this(ProofIndependentSettings.DEFAULT_INSTANCE.getTestGenerationSettings());
	}
	
	@Override
    protected void createComponents() {
	   getSaveToFilePanel();
	   getMaxProcesses();
	   getMaxUnwinds();
	   getInvariantForall();
	   getRemoveDuplicatesPanel();
	   getJUnitPanel();	   
	    
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

				}
			});
		}
		return saveToFilePanel;
	}
	
	public JCheckBox getJUnitPanel(){
		if(useJUnit == null){
			
			useJUnit = addCheckBox("Generate JUnit", infoUseJunit, settings.useJunit(), new ActionListener() {
				@Override
				public void actionPerformed(ActionEvent e) {
					settings.setUseJunit(useJUnit.isSelected());
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
				}
			});
		}
		return removeDuplicates;
	}
	
	public JCheckBox getInvariantForall(){
		
		if(invariantForAll == null){
			
			invariantForAll = addCheckBox("Require invariant for all objects", infoInvariantForAll, settings.invaraiantForAll(), new ActionListener() {
				@Override
				public void actionPerformed(ActionEvent e) {
					settings.setInvariantForAll(invariantForAll.isSelected());
				}
			});
			
			
		}
		
		return invariantForAll;
		
		
	}
	
	
	
}