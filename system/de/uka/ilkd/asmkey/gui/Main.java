// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.gui;

import jargs.gnu.CmdLineParser;

import java.awt.BorderLayout;
import java.awt.event.*;
import java.io.File;
import java.io.IOException;

import javax.swing.*;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import de.uka.ilkd.asmkey.storage.StorageException;
import de.uka.ilkd.asmkey.storage.StorageManager;
import de.uka.ilkd.asmkey.unit.*;
import de.uka.ilkd.asmkey.util.AsmKeYResourceManager;
import de.uka.ilkd.key.gui.SwingWorker;
import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.parser.ParserException;

/**
 * in AsmKeY, the main window consists of the 
 * project viewer that shows all the units contained
 * in the current project.
 */
public class Main extends JFrame {

    private StorageManager storageManager;
    private UnitManager unitManager;
    private String currentProject;
    private Unit selectedUnit;
    private ProverFrame proverFrame;

    private JList unitsPanel;
    private JList elementsPanel;
    private JTextArea contentsPanel;
    private JSplitPane splitPane1, splitPane2;

    protected final String keyhome = AsmKeYResourceManager.getInstance().getKeyHomePath();


    protected Main(StorageManager storageManager, ProverFrame proverFrame) {
	super("AsmKey");

	this.storageManager = storageManager;
	this.proverFrame = proverFrame;
	this.selectedUnit = null;
	
	proverFrame.setMain(this);
	setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);
	layoutMain();
	setSize(1000,750);
	addWindowListener(new MainListener());
	SwingUtilities.updateComponentTreeUI(this);
	setVisible(true);
	resetGUI();
    }

    public UnitManager unitManager() {
	return unitManager;
    }

    private void layoutMain() {
	

	/* layout for the whole frame */
	getContentPane().setLayout(new BorderLayout());

	setJMenuBar(new JMenuBar());
	buildMenu();
	
	unitsPanel = new JList();
	unitsPanel.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
	unitsPanel.addListSelectionListener(new ListSelectionListener() {
		public void valueChanged(ListSelectionEvent e) {
		    unitChanged((Unit) ((JList)e.getSource()).getSelectedValue());
		}
	    });
	elementsPanel = new JList();
	elementsPanel.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
	elementsPanel.addListSelectionListener(new ListSelectionListener() {
		public void valueChanged(ListSelectionEvent e) {
		    propChanged((PropositionIntern) ((JList)e.getSource()).getSelectedValue());
		}
	    });
	elementsPanel.addMouseListener(new MouseAdapter() {
		public void mouseClicked(MouseEvent e) {
		    if (e.getClickCount() == 2) {
			propActivated((PropositionIntern)
				      ((JList)e.getSource()).getSelectedValue());
		    }
		}
	    });
	contentsPanel = new JTextArea();
	contentsPanel.setEditable(false);

	splitPane1 = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT,
				   elementsPanel, contentsPanel);
	splitPane2 = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT,
				   unitsPanel, splitPane1);

	getContentPane().add(splitPane2, BorderLayout.CENTER);
	
	

    }

    private void buildMenu() {
	JMenu menu;
	JMenuItem item;

	/* --- asmkey menu --- */
	
	menu = new JMenu("AsmKey");

	item = new JMenuItem("About AsmKey", KeyEvent.VK_A);
	menu.add(item);
	
	menu.addSeparator();

	item = new JMenuItem("Preferences", KeyEvent.VK_P);
	menu.add(item);
	
	menu.addSeparator();

	item = new JMenuItem("Quit", KeyEvent.VK_Q);
	//item.setAccelerator(KeyStroke.getKeyStroke("ctrl Q"));
	item.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    exitMain();
		}
	    });
	menu.add(item);

	getJMenuBar().add(menu);

	/* -- project menu -- */

	menu = new JMenu("Project");
	    
	item = new JMenuItem("Change project...", KeyEvent.VK_C);
	item.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    changeProject();
		}
	    });
	menu.add(item);
	getJMenuBar().add(menu);
	
	/* --- windows menu --- */
	
	menu = new JMenu("Windows");
	getJMenuBar().add(menu);
	
    }

    private void resetGUI() {
	unitsPanel.setListData(new Object[0]);
	elementsPanel.setListData(new Object[0]);
	contentsPanel.setText("");
	splitPane1.setDividerLocation(1.0/3.0);
	splitPane2.setDividerLocation(1.0/4.0);
    }

    private void changeProject() {
	String newProject = (String) JOptionPane.showInputDialog
	    (this,
	     "Choose a project",
	     "Choose a project",
	     JOptionPane.PLAIN_MESSAGE,
	     null,
	     storageManager.getProjectIds(),
	     project());
	if (newProject != null) {
	    SetProjectWorker worker = new SetProjectWorker(newProject, this);
	    stopInterface();
	    worker.start();
	}
    }

    private void startInterface() {
	setCursor(new java.awt.Cursor(java.awt.Cursor.DEFAULT_CURSOR));
    }

    private void stopInterface() {
	setCursor(new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR));
    }

    private class SetProjectWorker extends SwingWorker {
	private String project;
	private Main main;
	
	public SetProjectWorker(String project, Main main) {
	    super();
	    assert project != null: "SetProjectWorker needs a non-null project.";
	    this.project = project;
	    this.main = main;
	}

	public Object construct() {
	    try {
		setProject(project);
		return null;
	    } catch (Exception e) {
		return e;
	    }
	}
	
	public void finished() {
	    Exception e = (Exception) get(); 
	    if (e != null && main != null) {
		if (e instanceof NonFatalException) {
		    JOptionPane.showMessageDialog
			(main,
			 ((NonFatalException)e).getLongMessage(),
			 e.getMessage(),
			 JOptionPane.ERROR_MESSAGE);
		} else {
		    e.printStackTrace();
		    JOptionPane.showMessageDialog
			(main,
			 e.toString() + " " + e.getMessage(),
			 "Unusual error.",
			 JOptionPane.ERROR_MESSAGE);
		}
	    }
	    startInterface();
	}
    }
    
    private class MainListener extends WindowAdapter {
	public void windowClosing(WindowEvent e) {
	    exitMain();	    
	}
    } 

    protected void exitMain() {
	System.exit(0);
    }
    
    public void setProject(String project) throws NonFatalException {
	boolean cont = true;
	if (this.currentProject != null) {
	    cont = closeCurrentProject();
	}
	selectedUnit = null;
	resetGUI();
	if (cont) {
	    this.currentProject = project;
	    if (project != null) {
		try {
		    openProject(project);
		} catch (NonFatalException e) {
		    this.currentProject = null;
		    throw e;
		}
	    } else {
		throw new NonFatalException("Update GUI for null", "");
	    }
	}
    }

    public String project() {
	return currentProject;
    }

    private boolean closeCurrentProject() {
	return true;
    }

    private void openProject(String project) throws NonFatalException {
	unitManager = new UnitManager
	    (storageManager, 
	     createUnitListener(),
             project,
	     proverFrame.mediator());
	try {
	    try {
		unitManager.loadUnits();
		unitsPanel.setListData(unitManager.getOrderedUnits());
	    } catch (UnitException e) {
		throw new InternalError(e.getMessage());
	    } catch (ParserException e) {
		throw new InternalError(e.getMessage() + "\nat location " + e.getLocation());
	    }
	} catch (InternalError e) {
	    unitManager = null;
	    throw new NonFatalException("The project " + project + " cannot be loaded",
					e.getMessage());
	}
    }

    private UnitListener createUnitListener() {
	try {
	    return TextUnitListener.fileUnitListener
		(new File(keyhome + "/system/unit_manager.log"));
	} catch (IOException e) {
	    System.out.println("Warning: " + e.getMessage());
	    return new UnitUtil.EmptyUnitListener();
	}
    }

    public void unitChanged(Unit unit) {
	if (unit != null) {
	    selectedUnit = unit;
	    int tacletLength = selectedUnit.tacletNS().elements().size();
	    int propLength = selectedUnit.lemmaNS().elements().size();
	    PropositionIntern[] props = new PropositionIntern[tacletLength + propLength];
	    IteratorOfNamed it = selectedUnit.tacletNS().elements().iterator();
	    for(int i=0; i<tacletLength; i++) {
		Named named = it.next();
		props[i] = new PropositionIntern(named, RestrictedSymbol.TACLET);
	    }
	    it = selectedUnit.lemmaNS().elements().iterator();
	    for(int i = tacletLength; i<tacletLength + propLength; i++) {
		Named named = it.next();
		props[i] = new PropositionIntern(named, RestrictedSymbol.PROPOSITION);
	    }
	    
	    elementsPanel.setListData(props);
	}
    }

    public void propChanged(PropositionIntern prop) {
	if (selectedUnit != null && prop!=null) {
	    contentsPanel.setText
		(prop.prop.toString());
	} else {
	    contentsPanel.setText("");
	}
    }

    public static class PropositionIntern implements Named {
	
	public Named prop;
	public int type;

	public PropositionIntern(Named prop, int type) {
	    this.prop = prop;
	    this.type = type;
	}

	public String toString() {
	    return prop.name().toString();
	}
	
	public Name name() {
	    return prop.name();
	}

    }
    
    public void propActivated(PropositionIntern prop) {
	if(prop != null) {
	    ProblemLoader loader = new ProblemLoader
		(prop.name(), this, proverFrame, unitManager);
	    loader.start();
	}
    }

    private static class InternalError extends Exception {
	public InternalError(String message) { super(message); }
    }

    /* --- static part  for main() --- */
    
    private static String projectAtStartup;
    private static String propAtStartup;
    private static boolean batchMode;

    public static void printVersion() {
	System.out.println("AsmKey, version haku");
	System.out.println("(c) haku and co.");
    }

    public static void printUsage() {
	printVersion();
	System.out.println("\nUsage: asmkey [options] [prop]");
	System.out.println("\nwhere [prop] has the form: Unit.proposition");
	System.out.println("\nwhere options are:");
	System.out.println("-d on|off | --debug on|off : debug mode (default off)");
	System.out.println("-a on|off | --assertions on|off : assertions (default on)");
	System.out.println("-b on|off | --batch on|off : auto/batch mode (default off)");
	System.out.println("-p name | --project name : select project");
	System.out.println("-h | --help : print this help");
	System.out.println("-v | --version : print version information");
    }

    public static void evaluateOptions(String[] args) {
	CmdLineParser parser = new CmdLineParser();
	CmdLineParser.Option debug = parser.addStringOption('d',"debug");
	CmdLineParser.Option assertion = parser.addStringOption('a',"assertion");
	CmdLineParser.Option batch = parser.addStringOption('b',"batch");
	CmdLineParser.Option project = parser.addStringOption('p', "project");
	CmdLineParser.Option help = parser.addBooleanOption('h', "help");
	CmdLineParser.Option version = parser.addBooleanOption('v', "version");

	try {
            parser.parse(args);
        }
        catch ( CmdLineParser.OptionException e ) {
            System.err.println(e.getMessage());
	    printUsage();
            System.exit(-1);
        }
	
	// Extract the values entered for the various options -- if the
        // options were not specified, the corresponding values will be
        // null.
        String debugValue = (String)parser.getOptionValue(debug, "off");
        String assertionValue = (String)parser.getOptionValue(assertion, "on");
	String batchValue = (String)parser.getOptionValue(batch, "off");
	Boolean helpValue = (Boolean)parser.getOptionValue(help, Boolean.FALSE);
	Boolean versionValue = (Boolean)parser.getOptionValue(version, Boolean.FALSE);
 
	projectAtStartup = (String)parser.getOptionValue(project);
		
	// if the user wanted help, print it and exit.
	if (helpValue.booleanValue()) {
	    printUsage();
	    System.exit(0);
	}

	// if the user wanted the version, print it
	if (versionValue.booleanValue()) {
	    printVersion();
	}

	batchMode = onOffToBoolean(batchValue);
	de.uka.ilkd.key.util.Debug.ENABLE_ASSERTION = onOffToBoolean(assertionValue);
	de.uka.ilkd.key.util.Debug.ENABLE_DEBUG = onOffToBoolean(debugValue);
	
	// Extract the trailing command-line arguments ('a_number') in the
        // usage string above.
        String[] otherArgs = parser.getRemainingArgs();
	if (otherArgs.length == 1) {
	    propAtStartup = otherArgs[0];
	} else if (otherArgs.length == 0) {
	    propAtStartup = null;
	} else {
	    printUsage();
	    System.exit(-1);
	}



	if (de.uka.ilkd.key.util.Debug.ENABLE_DEBUG) {
	    System.out.println("Running in debug mode ...");
	} else {
	    System.out.println("Running in normal mode ...");
	}
	if (de.uka.ilkd.key.util.Debug.ENABLE_ASSERTION) {
	    System.out.println("Using assertions ...");	   
	} else {
	    System.out.println("Not using assertions ...");	   
	}
	if (batchMode) {
	    System.out.println("Using auto/batch mode");
	}

    }
    
    private static boolean onOffToBoolean(String option) {
	if ((option == null) || option.equals("on")) {
	    return true;
	} else {
	    return false;
	}
    }


    public static void main(String[] args) {
	Main.evaluateOptions(args);
	de.uka.ilkd.key.gui.Main proverFrame = ProverFrame.getInstance();
	//key.loadCommandLineFile();
	try {
	    Main asmkey = new Main(new StorageManager
				   ("/home/nanchen/hood/research/asmkey"),
				   (ProverFrame) proverFrame);
	} catch (StorageException e) {
	    System.out.println("FATAL error: " + e.getMessage());
	    System.exit(-1);
	}
    }
}
