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
	private FileChooserPanel openJMLPanel;
	private FileChooserPanel objenesisPanel;
	private JTextField maxProcesses;
	private JTextField maxUnwinds;
	private JCheckBox useJUnit;
	private JCheckBox invariantForAll;
	private JCheckBox removeDuplicates;
	private JCheckBox checkboxRFL;

	private int minWidthOfTitle;
	
	private static final String infoSaveTo = "Choose the folder where the testcase files will be written.";
	private static final String infoMaxProcesses = "Maximal number of SMT processes that are allowed to run concurrently.";
	private static final String infoUseJunit = "Generate JUnit test suites (Test oracles not yet implemented).";
	private static final String infoInvariantForAll = "Require the invariant of all created objects to be true.";
	private static final String infoMaxUnwinds = "Maximal number of loop unwinds or method calls on a branch.";
	private static final String infoRemoveDuplicates = "Generate a single testcase for two ore more identical nodes.";
	private static final String infoRFLSelection = "Enables initialization of protected, private, and ghost fields with test data, " +
			                                       "as well as creation of objects from classes which have no default constructor." +
			                                       "This functionality is enabled by RFL.java which is generated along the test suite.";
	private static final String infoOpenJMLPath = "Set location of openjml.jar";
	private static final String infoObjenesisPath = "Set location of objenesis.jar";
	
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
	   getOpenJMLPanel();
	   getObjenesisPanel();
	   getMaxProcesses();
	   getMaxUnwinds();
	   getInvariantForall();
	   getRemoveDuplicatesPanel();
	   getRFLSelectionPanel();
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
			
			useJUnit = addCheckBox("Generate JUnit", infoUseJunit, settings.useJunit(), new ActionListener() {
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
	
	
	
}