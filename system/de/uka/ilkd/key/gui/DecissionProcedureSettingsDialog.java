package de.uka.ilkd.key.gui;

import java.awt.Component;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.WindowEvent;
import java.util.ArrayList;
import java.util.List;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import de.uka.ilkd.key.gui.DecisionProcedureSettings.RuleDescriptor;
import de.uka.ilkd.key.gui.configuration.ProofSettings;

/**
 * This Dialog is used to make changes in the configuration of Decision Procedures.
 * To make sure, the settings are consistent, it is realized as Singelton.
 * @author Simon Greiner
 *
 */
public class DecissionProcedureSettingsDialog extends JDialog {

    private static DecissionProcedureSettingsDialog instance;
    
    private List <RuleDescriptor> allrules;
    private JTextField nameField;
    private JTextField availableField;
    private JTextField executionField;
    private JList ruleDisplayList;
    private JCheckBox multiuseBox;
    
    private static final int LEFT_SIDE_WIDTH=190;
    private static final int RIGHT_SIDE_WIDTH=410;
    private static final int RULE_LIST_HEIGHT=305;
    
    /** Used for saving the settings temporally.*/
    class Settings{
	public boolean multipleProver;
	public String   executionCommand;
	public Settings(boolean multipleProver, String executionCommand) {
	    super();
	    this.multipleProver = multipleProver;
	    this.executionCommand = executionCommand;
	}
	    }
    
    private ArrayList<Settings> proverSettings=new ArrayList<Settings>();
    /**the index of the previous selected item in the list box*/
    private int                 previousSelectedIndex =-1;
    
    
    /**
     * Sets the preferred, maximum and minimum size of a <code>JComponent c</code> to <code>Dimension d</code>.
     * @param c  
     * @param d
     */
    private void setSize(JComponent c,Dimension d){
	c.setPreferredSize(d);
	c.setMaximumSize(d);
	c.setMinimumSize(d);	
    }
      
    
    /**
     * private constructor
     */
    private DecissionProcedureSettingsDialog() {
	super();
	this.setTitle("Decision Procedure Settings");
	this.init();
    }
    
    public static DecissionProcedureSettingsDialog getInstance() {
	if (instance == null) {
	    instance = new DecissionProcedureSettingsDialog();
	}
	return instance;
    }
    
    /** Call this method to reset the dialog to its original dimension.*/
    public static void resetInstance() {
	instance.setSize(400, 300);
	
	instance.reset();

	instance.setPreferredSize(new Dimension(LEFT_SIDE_WIDTH+RIGHT_SIDE_WIDTH, 370));
	instance.setMaximumSize(new Dimension(LEFT_SIDE_WIDTH+RIGHT_SIDE_WIDTH, 370));
	instance.setMinimumSize(new Dimension(LEFT_SIDE_WIDTH+RIGHT_SIDE_WIDTH, 370));
	instance.setVisible(true);
	
	
    }
    
    private void reset(){
	previousSelectedIndex = -1;
	proverSettings.clear();
	for (RuleDescriptor rd : this.allrules) {
		String cmd = ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().getExecutionCommand(rd);
		boolean b = ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().getMultipleUse(rd);
		proverSettings.add(new Settings(b,cmd));
	
	}
	this.setRuleVals();
    }
    
    private void init() {


	
	final int labelWidth = 110;
	final int fieldWidth = 270;
	final int labelHeight = 30;
	final int fieldHeight = 30;
	
	this.setResizable(true);
	
	
	JSplitPane tp = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT);
	
	//add the components to the panel
	JComponent lc = new JPanel();
	lc.setLayout(new BoxLayout(lc, BoxLayout.Y_AXIS));

	setSize(lc,new Dimension(LEFT_SIDE_WIDTH,RULE_LIST_HEIGHT));
	
	
	JComponent rc = new JPanel();
	rc.setLayout(new BoxLayout(rc, BoxLayout.Y_AXIS));
	setSize(rc,new Dimension(RIGHT_SIDE_WIDTH,RULE_LIST_HEIGHT));
	
	
	
	tp.setLeftComponent(lc);
	tp.setRightComponent(rc);
	this.allrules = ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().getAllRules();
	
	
	lc.add(buildDecprocList());
	lc.add(Box.createVerticalGlue());
	
	
	//add the settings-stuff for the selected decproc on the right
	Box globalBox = Box.createVerticalBox();
	
	JLabel nameLabel = new JLabel("Name");
	nameLabel.setAlignmentX(Component.LEFT_ALIGNMENT);
	setSize(nameLabel,new Dimension(labelWidth,labelHeight));
	
	nameField = new JTextField();
	setSize(nameField,new Dimension(fieldWidth,fieldHeight));
	nameField.setEditable(false);
	
	
	Box b = Box.createHorizontalBox();
	b.add(nameLabel);
	b.add(nameField);
	b.add(Box.createHorizontalGlue());
	
	globalBox.add(b);
	
	
	JLabel availableLabel = new JLabel("Installed");
	setSize(availableLabel,new Dimension(labelWidth,labelHeight));
	
	
	availableField = new JTextField();
	setSize(availableField,new Dimension(fieldWidth,fieldHeight));
	availableField.setEditable(false);
	
	
	b = Box.createHorizontalBox();
	b.add(availableLabel);
	b.add(availableField);
	b.add(Box.createHorizontalGlue());
	globalBox.add(b);
	
	JLabel execLabel = new JLabel("Command");
	setSize(execLabel,new Dimension(labelWidth,labelHeight));

	
	this.executionField = new JTextField();
	setSize(executionField,new Dimension(fieldWidth,fieldHeight));
	

	
	b = Box.createHorizontalBox();
	b.add(execLabel);
	b.add(executionField);
	b.add(Box.createHorizontalGlue());
	
	globalBox.add(b);
	
	
	
	this.multiuseBox = new JCheckBox();
	setSize(multiuseBox,new Dimension(fieldWidth+labelWidth,fieldHeight));
	this.multiuseBox.setText("use this prover for the rule 'multiple provers'");

	
	
	b = Box.createHorizontalBox();
	b.add(multiuseBox);
	b.add(Box.createHorizontalGlue());
	
	globalBox.add(b);
	

	
	this.reset();

	
	
	//add the description
	JTextArea c = new JTextArea("Editing the start command:\n" +
		"Specify the start command for an external procedure in\n such a way that it can be executed " +
		"to solve a problem file.\nFeel free to use any parameter to finetune the program.\n\n" +
		"Use %f as placeholder for the filename containing the \nproblemdescription.\n\n" +
		"Use %p as placeholder for the problem directly.\nThis should be needed in special cases only.");
	c.setBorder(new TitledBorder("Explanation"));
	c.setEditable(false);
	setSize(c,new Dimension(RIGHT_SIDE_WIDTH,RULE_LIST_HEIGHT-4*labelHeight));
	globalBox.add(c);
	
	
	
	globalBox.add(Box.createVerticalGlue());
	
	JButton applyButton = new JButton("apply");
	applyButton.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
		storeCommand();
	    }
	});
	JButton closeButton = new JButton("close");
	closeButton.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
		DecissionProcedureSettingsDialog.instance.setVisible(false);
	    }
	});
	JButton okayButton = new JButton("ok");
	okayButton.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
		storeCommand();
		DecissionProcedureSettingsDialog.instance.setVisible(false);
	    }
	});

	b = Box.createHorizontalBox();
	b.add(Box.createHorizontalGlue());
	b.add(applyButton);
	b.add(Box.createHorizontalStrut(5));
	b.add(okayButton);
	b.add(Box.createHorizontalStrut(5));
	b.add(closeButton);
	
	globalBox.add(b);
	
	rc.add(globalBox);
	

	this.add(tp);

	this.setVisible(true);
    }
    
    

    
    private void storeCommand() {
	
	int selectedIndex = ruleDisplayList.getSelectedIndex();
	Settings  set = proverSettings.get(selectedIndex);
	    set.multipleProver = this.multiuseBox.isSelected();
	    set.executionCommand = this.executionField.getText();
		
	for(int i=0; i<allrules.size(); i++){
	        RuleDescriptor rd = allrules.get(i);
		String command = proverSettings.get(i).executionCommand;
		boolean multipleuse = proverSettings.get(i).multipleProver;
		boolean fire = i == allrules.size()-1;
		ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().setMultipleUse(rd,multipleuse,false);
		ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().setExecutionCommand(rd, command,fire); 
	}
	
	

	
	Main.instance.updateDecisionProcedureSelectMenu();
	this.setRuleVals();
    }
    
/*    private void performTest() {
	RuleDescriptor rd = allrules.get(ruleDisplayList.getSelectedIndex());
	String command = this.executionField.getText();
	boolean result = ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().checkCommand(rd, command);
	if (result) {
	    System.out.println("### Test successful");
	} else {
	    System.out.println("### The test was not successfull");
	}
    }*/
    
    /**
     * set the value fields according to the values of the selected decproc.
     */
    private void setRuleVals() {
	if(previousSelectedIndex >= 0){
	    Settings  set = proverSettings.get(previousSelectedIndex);
	    set.multipleProver = this.multiuseBox.isSelected();
	    set.executionCommand = this.executionField.getText();
	}
	
	
	int selectedIndex = ruleDisplayList.getSelectedIndex();
	previousSelectedIndex = selectedIndex;
	RuleDescriptor rd = this.allrules.get(selectedIndex);
	this.nameField.setText(rd.getDisplayName());
	if (ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().isInstalled(rd)) {
	    this.availableField.setText("Yes");
	} else {
	    this.availableField.setText("No");
	}
	this.executionField.setText(proverSettings.get(selectedIndex).executionCommand);
	this.multiuseBox.setSelected(proverSettings.get(selectedIndex).multipleProver);
	

    }
    
    /**
     * Build a list that displays all available decprocs.
     * @return
     */
    private JList buildDecprocList() {
	ArrayList<String> rulenames = new ArrayList<String>();
	for (RuleDescriptor rd : this.allrules) {
		rulenames.add(rd.getDisplayName());
		
	}
	ruleDisplayList = new JList(rulenames.toArray());
	ruleDisplayList.setBorder(new TitledBorder("Decision Procedures"));
	ruleDisplayList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
	ruleDisplayList.setSelectedIndex(0);
	
	setSize(ruleDisplayList,new Dimension(LEFT_SIDE_WIDTH,RULE_LIST_HEIGHT));

	
	//add the selectionListener
	ruleDisplayList.addListSelectionListener(new ListSelectionListener () {
	    public void valueChanged(ListSelectionEvent e) {
		setRuleVals();
	    }
	});
	
	return ruleDisplayList;
    }
    
}
