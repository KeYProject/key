// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.smt;


import java.awt.Color;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.LinkedList;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JComponent;
import javax.swing.JScrollPane;
import javax.swing.JTextField;
import javax.swing.SwingUtilities;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;


import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.smt.SolverType;

public class SMTSettingsModel extends DefaultTreeModel {

	private final LinkedList<SolverOptions> solverOptions = new LinkedList<SolverOptions>();
	private OptionContentNode startNode;


	private final SMTSettings originalSettings;
	private final SMTSettings temporarySettings;

	public SMTSettingsModel(SMTSettings smtSettings) {
		super( new DefaultMutableTreeNode("Options"));
		originalSettings = smtSettings;
		temporarySettings = new SMTSettings(smtSettings.getPdSettings().clone(),
				smtSettings.getPiSettings().clone(), smtSettings.getProof());
		create((DefaultMutableTreeNode)this.getRoot(), temporarySettings);


	}

	public JComponent getStartComponent(){
		return startNode.getComponent();
	}


	public void apply(){
		originalSettings.copy(temporarySettings);
		originalSettings.fireSettingsChanged();
		for(SolverOptions options : solverOptions){
			options.updateOptions();
		}
	}

	public void storeAsDefault(){
		ProofSettings.DEFAULT_SETTINGS.getSMTSettings().copy(temporarySettings.getPdSettings());
	}
	private static final long serialVersionUID = 1L;

	private DefaultMutableTreeNode create(DefaultMutableTreeNode optionsNode, SMTSettings smtSettings){
		OptionContentNode generalOptionsNode =  new OptionContentNode("General",
				new JScrollPane(new GeneralOptions(smtSettings.getPiSettings())));

		OptionContentNode translationOptionsNode =  new OptionContentNode("SMT-Translation",
				new JScrollPane(new TranslationOptions(smtSettings.getPdSettings())));

		OptionContentNode tacletTranslationOptionsNode =  new OptionContentNode("Taclet Translation",
				new JScrollPane(new TacletTranslationOptions(smtSettings)));
		startNode = generalOptionsNode;

		solverOptions.add(new SolverOptions(SolverType.Z3_SOLVER,smtSettings.getPiSettings()));
		solverOptions.add(new SolverOptions(SolverType.YICES_SOLVER,smtSettings.getPiSettings()));
		solverOptions.add(new SolverOptions(SolverType.SIMPLIFY_SOLVER,smtSettings.getPiSettings()));
		solverOptions.add(new SolverOptions(SolverType.CVC3_SOLVER,smtSettings.getPiSettings()));



		optionsNode.add(generalOptionsNode);
		optionsNode.add(translationOptionsNode);
		tacletTranslationOptionsNode.add(new OptionContentNode("Selection",
				new JScrollPane((new TacletTranslationSelection(smtSettings)).getSelectionTree())));
		optionsNode.add(tacletTranslationOptionsNode);

		for(SolverOptions options : solverOptions){
			optionsNode.add(new OptionContentNode(options.getName(),
					new JScrollPane(options)));  
		}

		return optionsNode;


	}

}



class GeneralOptions extends TablePanel{
	private static final long serialVersionUID = 1L;
	private FileChooserPanel saveToFilePanel;
	private JComboBox        progressModeBox;
	private JTextField       maxProcesses;
	private JTextField       timeoutField;
	private JTextField intBoundField;
	//private JTextField heapBoundField;
	private JTextField seqBoundField;
	private JTextField objectBoundField;
	private JTextField locsetBoundField;
	
	private JCheckBox  solverSupportCheck;
	private final ProofIndependentSMTSettings settings;

	public final static String PROGRESS_MODE_USER = "Progress dialog remains open after executing solvers.";
	public final static String PROGRESS_MODE_CLOSE = "Close progress dialog after all solvers have finished.";
	public final static String PROGRESS_MODE_CLOSE_FIRST = "Close progress dialog after the first solver has finished.";
	public final int minWidthOfTitle;

	private final static String infoBound = "Bitvector size for this type. Use a value larger than 0.";
	
	
	private final static String infoSaveToFilePanel = "Activate this option to store the translations "
			+ "that are handed over to the externals solvers:\n"
			+ "1. Choose the folder.\n"
			+ "2. Specify the filename:\n"
			+ "\t%s: the solver's name\n"
			+ "\t%d: date\n"
			+ "\t%t: time\n"
			+ "\t%i: the goal's number\n"
			+ "\n\n"
			+ "Example: /home/translations/%d_%t_%i_%s.txt"
			+ "\n\n"
			+ "Remark: After every restart of KeY this option "
                        + "is deactivated.";
			private final static String infoProgressModeBox = "1. Option: The progress dialog remains open "
					+ "after executing the solvers so that the user "
					+ "can decide whether he wants to accept the results.\n"
					+ "\n"
					+ "2. Option: The progress dialog is closed once the "
					+ "external provers have done their work or the time limit "
					+ "has been exceeded.\n";// +
			private static final String infoCheckForSupport = "If this option is activated, each time before a solver is started" +
					" it is checked whether the version of that solver is supported. If the version is not supported, a warning is" +
					" presented in the progress dialog.";

        private final static String infoMaxProcesses = "Maximal number or processes that are allowed to run concurrently.";
			private final static String infoTimeoutField = "Timeout for the external solvers in seconds. Fractions of a second are allowed.\n"
                        + "Example: 6.5";

					public GeneralOptions(ProofIndependentSMTSettings settings) {
						super();
						this.minWidthOfTitle = SwingUtilities.computeStringWidth(this.getFontMetrics(getFont()),"Concurrent ProcessesBLANK");
						this.settings = settings;
						createTable();
					}

					@Override
					protected void createComponents() {
						getSaveToFilePanel();
						getProgressModeBox();
						getTimeoutField();
						getMaxProcesses();
						getBoundFields();
						getSolverSupportCheck();

					}

					public JTextField getMaxProcesses() {
						if(maxProcesses == null){
							maxProcesses = addTextField("Concurrent Processes:",minWidthOfTitle,Long.toString(settings.maxConcurrentProcesses),infoMaxProcesses,
									new ActionListener(){

								@Override
								public void actionPerformed(
										ActionEvent e) {
									int value;
									try {
										value = Integer.parseInt(maxProcesses.getText());
									} catch (NumberFormatException ex) {
										value = settings.maxConcurrentProcesses;
									}
									settings.maxConcurrentProcesses = value;
								}                                
							});
						}
						return maxProcesses;
					}

					public JTextField getTimeoutField() {
						if(timeoutField == null){
							timeoutField = addTextField("Timeout:",minWidthOfTitle,Float.toString((float)settings.timeout/1000),infoTimeoutField,
									new ActionListener(){

								@Override
								public void actionPerformed(
										ActionEvent e) {
									long value;
									try {
										value = (long)(Float.parseFloat(timeoutField.getText())*1000);
									} catch (NumberFormatException ex) {
										value = settings.timeout;
									}
									settings.timeout = value;
								}                                
							});
						}
						return timeoutField;
					}
					
					public void getBoundFields() {
						if(intBoundField == null){
							intBoundField = addTextField("Integer Bound:",minWidthOfTitle,Long.toString(settings.intBound),infoBound,
									new ActionListener(){

								@Override
								public void actionPerformed(
										ActionEvent e) {
									long value;
									try {
										value = Long.parseLong(intBoundField.getText());
									} catch (NumberFormatException ex) {
										value = settings.intBound;
									}
									settings.intBound = value;
								}                                
							});
						}
						
						if(seqBoundField == null){
							seqBoundField = addTextField("Seq Bound:",minWidthOfTitle,Long.toString(settings.seqBound),infoBound,
									new ActionListener(){

								@Override
								public void actionPerformed(
										ActionEvent e) {
									long value;
									try {
										value = Long.parseLong(seqBoundField.getText());
									} catch (NumberFormatException ex) {
										value = settings.seqBound;
									}
									settings.seqBound = value;
								}                                
							});
						}
						if(objectBoundField == null){
							objectBoundField = addTextField("Object Bound:",minWidthOfTitle,Long.toString(settings.objectBound),infoBound,
									new ActionListener(){

								@Override
								public void actionPerformed(
										ActionEvent e) {
									long value;
									try {
										value = Long.parseLong(objectBoundField.getText());
									} catch (NumberFormatException ex) {
										value = settings.objectBound;
									}
									settings.objectBound = value;
								}                                
							});
						}
						if(locsetBoundField == null){
							locsetBoundField = addTextField("Locset Bound:",minWidthOfTitle,Long.toString(settings.locsetBound),infoBound,
									new ActionListener(){

								@Override
								public void actionPerformed(
										ActionEvent e) {
									long value;
									try {
										value = Long.parseLong(locsetBoundField.getText());
									} catch (NumberFormatException ex) {
										value = settings.locsetBound;
									}
									settings.locsetBound = value;
								}                                
							});
						}
						
					}
					
					 



					public JComboBox getProgressModeBox() {
						if(progressModeBox == null){
							progressModeBox = addComboBox(infoProgressModeBox,settings.modeOfProgressDialog, new ActionListener() {

								@Override
								public void actionPerformed(ActionEvent e) {
									settings.modeOfProgressDialog = progressModeBox.getSelectedIndex();
								}
							}, 
							getProgressMode(ProofIndependentSMTSettings.PROGRESS_MODE_USER),
							getProgressMode(ProofIndependentSMTSettings.PROGRESS_MODE_CLOSE));
						}
						return progressModeBox;
					}

					public JCheckBox getSolverSupportCheck() {
						if(solverSupportCheck == null){
							solverSupportCheck = addCheckBox("Check for support when a solver is started.",
									infoCheckForSupport,
									settings.checkForSupport
									, new ActionListener() {
								@Override
								public void actionPerformed(ActionEvent e) {
									settings.checkForSupport = solverSupportCheck.isSelected(); 
								}
							});
						}    

						return solverSupportCheck;
					}


					public FileChooserPanel getSaveToFilePanel() {
						if(saveToFilePanel == null){
							saveToFilePanel = addFileChooserPanel("Store translation to file:",
									settings.pathForSMTTranslation, infoSaveToFilePanel, 
                                        true,settings.storeSMTTranslationToFile,new ActionListener() {

								@Override
								public void actionPerformed(ActionEvent e) {
									settings.pathForSMTTranslation = saveToFilePanel.getPath();
									settings.storeSMTTranslationToFile = saveToFilePanel.isSelected();

								}
							});
						}
						return saveToFilePanel;
					}





					public String getProgressMode(int index) {
						switch (index) {
						case ProofIndependentSMTSettings.PROGRESS_MODE_USER:
							return PROGRESS_MODE_USER;
						case ProofIndependentSMTSettings.PROGRESS_MODE_CLOSE:
							return PROGRESS_MODE_CLOSE;
						case ProofIndependentSMTSettings.PROGRESS_MODE_CLOSE_FIRST:
							return PROGRESS_MODE_CLOSE_FIRST;
						}
						return "";
					}

}

class SolverOptions extends TablePanel{
	private static final long serialVersionUID = 1L;
	private JTextField solverName;
	private JTextField solverCommand;
	private JTextField solverParameters;
	private JTextField solverInstalled;
	private JTextField solverSupported;
	private JButton    toDefaultButton;


	private JButton    checkForSupportButton;

	private final SolverType solverType; 
	private final ProofIndependentSMTSettings settings;

	private final int minWidthOfTitle;

	private static final String infoSolverName =
			"There are two ways to make supported provers applicable for KeY:\n"
					+ "1. Specify the absolute path of the prover in the field 'Command'.\n"
					+ "2. Change the environment variable $PATH of your system, so that it "
					+ "refers to the installed prover. In that case you must specify the name of the solver in 'Command'";

	private static final String infoSolverParameters ="In this field you can specify which parameters are passed to the " +
			"solver when the solver is started. Note that the default parameters are crucial for a stable run of the" +
			"solver.";
	private static final String infoSolverCommand ="The command for the solver.\n\n" +
			"Either you specify the absolute path of your solver or just the command for starting it.\n" +
			"In the latter case you have to modify the PATH-variable of your system.\n" +
			"Please note that you also have to specify the filename extension\n" +
			"For example: z3.exe";

	private static final String infoSolverSupport = "For the KeY system only some particular versions of this solver " +
			"have been tested. It is highly recommended to use those versions, because otherwise it is not guaranteed that " +
			"the connection to this solver is stable.\n\n" +
			"If you want to check whether the installed solver is supported, please click on the button below.\n\n";



	private static final String solverSupportText[] = {"Version of solver is supported.",
		"Version of solver may not be supported.",
	"Support has not been checked, yet."};
	private static final int SOLVER_SUPPORTED = 0;
	private static final int SOLVER_NOT_SUPPOTED = 1;
	private static final int SOLVER_SUPPORT_NOT_CHECKED = 2;

	public SolverOptions(SolverType solverType,ProofIndependentSMTSettings settings) {
		super();
		this.minWidthOfTitle = SwingUtilities.computeStringWidth(this.getFontMetrics(getFont()),"InstalledBLANK");
		this.setName(solverType.getName());
		this.solverType = solverType;
		this.settings = settings;

		createTable();

		if(solverType.getInfo() != null){
			getInfoText().setText(solverType.getInfo());
		}
	}

	@Override
	protected void updateOptions() {
		getSolverInstalled().setText(Boolean.toString(solverType.isInstalled(true)));
		if(checkForSupportButton != null){
			checkForSupportButton.setEnabled(solverType.isInstalled(false));
		}
	}


	@Override
	protected void createComponents() {
		getSolverName();
		getSolverInstalled();
		getSolverCommand();
		getSolverParameters();
		getSolverSupported();
		createButtons();


	}




	public void createButtons() {
		toDefaultButton = new JButton("Set parameters to default.");

		toDefaultButton.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent arg0) {
				getSolverParameters().setText(solverType.getDefaultSolverParameters());
				settings.setParameters(solverType, solverParameters.getText());  

			}
		});


		checkForSupportButton = new JButton("Check for support.");
		checkForSupportButton.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent arg0) {
				solverType.checkForSupport();
				getSolverSupported().setText(getSolverSupportText());
			}
		}); 
		checkForSupportButton.setEnabled(solverType.isInstalled(false));

		Box box  = addComponent(null,toDefaultButton,checkForSupportButton);

		box.add(Box.createHorizontalGlue());


	}



	private String createSupportedVersionText(){
		String [] versions =solverType.getSupportedVersions();
		String result = versions.length>1 ? "The following versions are supported: " :	
			"The following version is supported: ";
		for(int i=0; i < versions.length; i++){
			result += versions[i];
			result += i<versions.length-1 ? ", ":"";
		}
		return result;
	}

	private String getSolverSupportText(){
		if(solverType.supportHasBeenChecked()){
			return solverType.isSupportedVersion() ? solverSupportText[SOLVER_SUPPORTED] : solverSupportText[SOLVER_NOT_SUPPOTED];
		}else{
			return solverSupportText[SOLVER_SUPPORT_NOT_CHECKED];
		}
	}

	public JTextField getSolverSupported() {
		if(solverSupported == null){
			solverSupported = addTextField("Support",minWidthOfTitle,getSolverSupportText(),
					infoSolverSupport+createSupportedVersionText(),null);
			solverSupported.setEditable(false);

		}
		return solverSupported;
	}


	public JTextField getSolverParameters() {
		if(solverParameters == null){
			solverParameters = addTextField("Parameters",minWidthOfTitle,solverType.getSolverParameters(),infoSolverParameters,new ActionListener() {

				@Override
				public void actionPerformed(ActionEvent e) {
					settings.setParameters(solverType, solverParameters.getText());                                      
				}
			});
		}
		return solverParameters;
	}

	public JTextField getSolverCommand() {
		if(solverCommand == null){
			solverCommand = addTextField("Command",minWidthOfTitle,solverType.getSolverCommand()
					,infoSolverCommand,new ActionListener() {

				@Override
				public void actionPerformed(ActionEvent e) {
					settings.setCommand(solverType, solverCommand.getText());                                      
				}
			});
		}
		return solverCommand;
	}


	public JTextField getSolverInstalled() {
		if(solverInstalled == null){
                    final boolean installed = solverType.isInstalled(true);
                    String info = installed? "yes": "no";
                    if (installed) {
                        final String versionString = solverType.getRawVersion();
                        info = info + (versionString.startsWith("version")? " (": " (version ")+ versionString + ")";
                    }
                    solverInstalled = addTextField("Installed",minWidthOfTitle,info,"",null);
			solverInstalled.setBackground(this.getBackground());
			solverInstalled.setEditable(false);
		}
		return solverInstalled;
	}

	public JTextField getSolverName() {
		if(solverName == null){
			solverName = addTextField("Name",minWidthOfTitle,solverType.getName(),infoSolverName,null);
			solverName.setBackground(this.getBackground());
			solverName.setEditable(false);
		}
		return solverName;
	}

}

class TacletTranslationOptions extends TablePanel{
	private static final long serialVersionUID = 1L;
	private FileChooserPanel fileChooserPanel;
	private final SMTSettings settings;
	private JTextField       maxNumberOfGenerics;
	private final int minWidthOfTitle;

	private static final String infoFileChooserPanel = "Activate this option to store the translations of taclets"
			+ " that are handed over to the externals solvers:\n"
			+ "1. Choose the folder.\n"
			+ "2. Specify the filename:\n"
			+ "\t%s: the solver's name\n"
			+ "\t%d: date\n"
			+ "\t%t: time\n"
			+ "\t%i: the goal's number\n"
			+ "\n\n"
			+ "Example: ./home/translations/Taclet%d_%t_%i_%s.txt"
			+ "\n\n"
			+ "Note: After every restart of KeY this option"
			+ " is deactivated.";

	private static final String infoMaxNumberOfGenerics =      

			"This option specifies how many different generic sorts are allowed"
					+ " within a taclet.\n\n"
					+ "Be aware of the fact that too many different generic sorts can"
					+ " overwhelm the external solvers. On the other side there are taclets that"
					+ " use a certain amount of different generic sorts (see: taclet selection).\n\n"
					+ "Rule of thumb: Most of the taclets can be translated by using 2-3 different"
					+ " generic sorts.";


	public TacletTranslationOptions(SMTSettings settings) {
		super();
		this.minWidthOfTitle = SwingUtilities.computeStringWidth(this.getFontMetrics(getFont()),"Maximum number of generic sorts.BLANK");
		this.settings = settings;
		createTable();
	}


	@Override
	protected void createComponents() {
		createFileChooserPanel();
		createMaxNumberOfGenerics();

	}

	public JTextField createMaxNumberOfGenerics() {
		if(maxNumberOfGenerics == null){
			maxNumberOfGenerics = addTextField("Maximum number of generic sorts.",minWidthOfTitle,
					Integer.toString(settings.getMaxNumberOfGenerics())
					, infoMaxNumberOfGenerics, new ActionListener() {

				@Override
				public void actionPerformed(ActionEvent e) {
					int value;
					try {
						value = Integer.parseInt(maxNumberOfGenerics.getText());
					} catch (NumberFormatException ex) {
						value = settings.getPdSettings().maxGenericSorts;
					}
					settings.getPdSettings().maxGenericSorts = value;

				}
			});
		}
		return maxNumberOfGenerics;
	}


	public FileChooserPanel createFileChooserPanel() {
		if(fileChooserPanel == null){
			fileChooserPanel = addFileChooserPanel("Store taclet translation to file:",
					settings.getPathForTacletTranslation(),
					infoFileChooserPanel, true,settings.storeTacletTranslationToFile(),new ActionListener() {

				@Override
				public void actionPerformed(ActionEvent e) {
					settings.getPiSettings().pathForTacletTranslation = fileChooserPanel.getPath();
					settings.getPiSettings().storeTacletTranslationToFile = fileChooserPanel.isSelected();
				}
			});

		}
		return fileChooserPanel;
	}




}



class TranslationOptions extends TablePanel{
	private static final long serialVersionUID = 1L;
	private JCheckBox useExplicitTypeHierachy;
	private JCheckBox useNullInstantiation;
	private JCheckBox useBuiltInUniqueness;
	private JCheckBox useUIMultiplication;
	private JCheckBox useConstantsForIntegers;
	private JTextField minField;
	private JTextField maxField;
	private final int minWidthOfTitle;
	private final ProofDependentSMTSettings settings;

	private static final String infoUseExplicitTypeHierarchy = "If this option is selected, the transitive inheritance between classes is modeled by "
			+ "assumptions.\n\n"
			+ "Example: Let A, B and C  be classes such that C extends B and B extends A.\n"
			+ "If the option is not selected, the following assumptions are added:\n"
			+ "\\forall x; (type_of_C(x)->type_of_B(x))\n"
			+ "\\forall x; (type_of_B(x)->type_of_A(x))\n"
			+ "If the option is selected, the following assumption is additionally added to the assumptions above:\n"
			+ "\\forall x; (type_of_C(x)->type_of_A(x))\n";

	private static final String infoUseNullInstantiation =  
			"At the moment this option has only effect on hierarchy assumptions regarding the null object.\n"
					+ "Example: Let A and B be classes.\n"
					+ "If the option is not selected, the type null is treated as a normal class. "
					+ "Consequently, the following assumptions are added:\n"
					+ "\\forall x; (type_of_Null(x)->type_of_A(x))\n"
					+ "\\forall x; (type_of_Null(x)->type_of_B(x))\n"
					+ "If the option is selected, those assumptions are instantiated with a concrete null object:\n"
					+ "type_of_A(null)\n"
					+ "type_of_B(null)";
	private static final String infoUseBuiltInUniqueness =
			"Some solvers support the uniqueness of functions by built-in mechanisms. If this option is selected "
					+ "those mechanisms are used, otherwise some assumptions are added by using normal FOL.\n"
					+ "Note: The uniqueness of functions is needed for translating attributes and arrays.";
	private static final String infoUseUIMultiplication = 
			"Some solvers support only simple multiplications. For example Yices supports only multiplications of type a*b"
					+ " where a or b must be a number.\n"
					+ "In order to support more complex multiplications, this option can be activated: If the solver does not support a"
					+ " certain kind of multiplication, the occurence of this multiplication is translated"
					+ " into the uninterpreted function mult. Furthermore some"
					+ " typical assumptions are added:\n"
					+ "\\forall x; mult(x,0)=0\n"
					+ "\\forall x; mult(0,x)=0\n"
					+ "\\forall x; mult(x,1)=x\n"
					+ "\\forall x; mult(1,x)=x\n"
					+ "\\forall x; \\forall y; mult(x,y)=mult(y,x)\n"
					+ "\\forall x; \\forall y; \\forall z; mult(mult(x,y),z)=mult(x,mult(y,z))\n"
					+ "\\forall x; \\forall y; mult(x,y)=0 -> (x=0|y=0)\n"
					+ "\\forall x; \\forall y; mult(x,y)=1 -> (x=1&y=1)\n"
					+ "Note:\n"
					+ "1. If this option is not selected, an exception is thrown in the case that a unsupported multiplication "
					+ "occurs.\n"
					+ "2. The translation makes the uninterpreted function mult unique, so that there cannot be any clashes with functions"
					+ " that are introduced by the user.";
	private static final String infoUseConstantsForIntegers =
			"Some solvers support only a certain interval of integers (e.g. Simplify). If this option is activated,"
					+ " numbers that are not supported by the used solver are translated into uninterpreted constants. Furthermore "
					+ " an asumption is added that states that the introduced constant is greater than the maximum of the supported numbers.\n\n"
					+ "Example: Assume that a solver supports numbers less or equal 10:\n"
					+ "The number 11 is translated into the constant c_11 and the assumption"
					+ " c_11>10 is introduced.\n\n"
					+ "Note: If this option is not selected, an exception is thrown in the case that a not supported number occurs.\n";




	public TranslationOptions(ProofDependentSMTSettings settings) {
		super();
		this.minWidthOfTitle = SwingUtilities.computeStringWidth(this.getFontMetrics(getFont()),"MaximumBLANK");
		this.settings = settings;      
		createTable();

	}

	protected void createComponents(){
		createUseExplicitTypeHierachy();
		createNullInstantiation();
		createBuiltInUniqueness();
		createUIMultiplication();
		createConstantsForIntegers();
	}

	public JCheckBox createUseExplicitTypeHierachy() {
		if(useExplicitTypeHierachy == null){
			useExplicitTypeHierachy = addCheckBox("Use a explicit type hierarchy.",
					infoUseExplicitTypeHierarchy,
					settings.useExplicitTypeHierarchy
					, new ActionListener() {
				@Override
				public void actionPerformed(ActionEvent e) {
					settings.useExplicitTypeHierarchy = useExplicitTypeHierachy.isSelected(); 
				}
			});
		}
		return useExplicitTypeHierachy;
	}

	public JCheckBox createNullInstantiation() {
		if(useNullInstantiation == null){
			useNullInstantiation = addCheckBox("Instantiate hierarchy assumptions if possible (recommended).",
					infoUseNullInstantiation
					,settings.useNullInstantiation
					, new ActionListener() {
				@Override
				public void actionPerformed(ActionEvent e) {
					settings.useNullInstantiation = useNullInstantiation.isSelected(); 
				}
			});
		}
		return useNullInstantiation;
	}

	public JCheckBox createBuiltInUniqueness() {
		if(useBuiltInUniqueness == null){
			useBuiltInUniqueness = addCheckBox("Use built-in mechanism for uniqueness if possible.",
					infoUseBuiltInUniqueness
					,settings.useBuiltInUniqueness
					, new ActionListener() {
				@Override
				public void actionPerformed(ActionEvent e) {
					settings.useBuiltInUniqueness = useBuiltInUniqueness.isSelected(); 
				}
			});
		}
		return useBuiltInUniqueness;
	}

	public JCheckBox createUIMultiplication() {

		if(useUIMultiplication == null){
			useUIMultiplication = addCheckBox( "Use uninterpreted multiplication if necessary.", 
					infoUseUIMultiplication
					,settings.useUIMultiplication
					, new ActionListener() {
				@Override
				public void actionPerformed(ActionEvent e) {
					settings.useUIMultiplication = useUIMultiplication.isSelected(); 
				}
			});
		}
		return useUIMultiplication;
	}



	public JCheckBox createConstantsForIntegers() {

		if(useConstantsForIntegers == null){
			Box box = Box.createVerticalBox();

			box.setBorder(BorderFactory.createTitledBorder("Use constants for too big or too small integers."));

			maxField = createTextField(Long.toString(settings.maxInteger), new ActionListener() {

				@Override
				public void actionPerformed(ActionEvent e) {
					long result = settings.maxInteger;
					try{
						result = Long.parseLong(maxField.getText());
						maxField.setForeground(Color.BLACK);
					}catch(Throwable ex){
						maxField.setForeground(Color.RED);
					}
					settings.maxInteger = result;

				}
			});

			minField = createTextField(Long.toString(settings.minInteger), new ActionListener() {

				@Override
				public void actionPerformed(ActionEvent e) {
					long result = settings.minInteger;
					try{
						result = Long.parseLong(minField.getText());
						minField.setForeground(Color.BLACK);
					}catch(Throwable ex){
						minField.setForeground(Color.RED);
					}
					settings.minInteger = result;

				}
			});





			useConstantsForIntegers = createCheckBox("activated"
					,settings.useConstantsForIntegers
					, new ActionListener() {
						@Override
						public void actionPerformed(ActionEvent e) {
							settings.useConstantsForIntegers = useConstantsForIntegers.isSelected(); 
							maxField.setEnabled(useConstantsForIntegers.isSelected());
							minField.setEnabled(useConstantsForIntegers.isSelected());
						}
					});
			Box box2 = Box.createHorizontalBox();
			box2.add(useConstantsForIntegers);
			box2.add(Box.createHorizontalGlue());
			box.add(  box2);
			box.add(createTitledComponent("Maximum:",minWidthOfTitle, maxField));
			box.add(Box.createVerticalStrut(3));
			box.add(createTitledComponent("Minimum:",minWidthOfTitle, minField));


			addComponent(infoUseConstantsForIntegers,box);
		}
		return useConstantsForIntegers;
	}
}