package de.uka.ilkd.key.gui;

import java.awt.Component;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ArrayList;

import javax.swing.*;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.SetAsListOfProgramMethod;
import de.uka.ilkd.key.logic.op.SetOfProgramMethod;
import de.uka.ilkd.key.unittest.UnitTestBuilder;


public class MethodSelectionDialog extends JDialog {

    private UnitTestBuilder testBuilder;
    private KeYMediator mediator; 
    private JList methodList;
    private ArrayList<JCheckBox> RuleBoxes = new ArrayList<JCheckBox>();
    private static MethodSelectionDialog instance=null;
    private StringBuffer latestTests=new StringBuffer();

    private MethodSelectionDialog(KeYMediator mediator){
	this.mediator = mediator;
	testBuilder = new UnitTestBuilder(mediator.getServices(), 
					  mediator.getProof());
	layoutMethodSelectionDialog();
	pack();
	setLocation(70, 70);
	setVisible(true);
    }

    public static MethodSelectionDialog getInstance(KeYMediator mediator){
	if(instance != null){
	    instance.setVisible(false);
	    instance.dispose();
	}
	instance = new MethodSelectionDialog(mediator);
	return instance;
    }

    private void layoutMethodSelectionDialog(){
	getContentPane().setLayout(new BoxLayout(getContentPane(), 
						 BoxLayout.Y_AXIS));
	final MethodSelectionDialog thisRef = this;
	// methodlist
	methodList = new JList();
	methodList.setCellRenderer(new DefaultListCellRenderer(){
		public Component getListCellRendererComponent(
		    JList list,
		    Object value,
		    int index,
		    boolean isSelected,
		    boolean cellHasFocus)
		    {
			if(value != null){
			    ProgramMethod pm = (ProgramMethod) value;
			    MethodDeclaration md = pm.getMethodDeclaration();
			    String params = md.getParameters().toString();
			    setText((md.getTypeReference() == null ? "void" : 
					md.getTypeReference().getName())+
				    " "+md.getFullName()+"("+
				    params.substring(1,params.length()-1)+")");
			    if (isSelected) {
				setBackground(list.getSelectionBackground());
				setForeground(list.getSelectionForeground());
			    }
			    else {
				setBackground(list.getBackground());
				setForeground(list.getForeground());
			    }
			    setEnabled(list.isEnabled());
			    setFont(list.getFont());
			    setOpaque(true);
			}
			return this;
		    }
	    });
	SetOfProgramMethod pms = 
	    testBuilder.getProgramMethods(mediator.getProof());
	methodList.setListData(pms.toArray());
	JScrollPane methodListScroll = new
	    JScrollPane(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED, 
			ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
	methodListScroll.getViewport().setView(methodList);
	methodListScroll.setBorder(
	    new TitledBorder("Methods occuring in Proof"));
	methodListScroll.setMinimumSize(new java.awt.Dimension(250, 400));
	getContentPane().add(methodListScroll);

	//buttons
	final JPanel buttonPanel = new JPanel();
	buttonPanel.setLayout(new BoxLayout(buttonPanel, BoxLayout.X_AXIS));
	JButton testAll = new JButton("Create Test For Proof");
	testAll.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    createTest(null);
		}
	    });
  	buttonPanel.add(testAll);
	JButton testSel = new JButton("Create Test For Selected Method(s)");
	testSel.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    if(methodList.getSelectedValues().length == 0){
			JOptionPane.showMessageDialog(
			    null, "Please select the method(s) first!",
			    "No Methods Selected", 
			    JOptionPane.ERROR_MESSAGE);
		    }else{
			createTest(methodList.getSelectedValues());
		    }
		}
	    });
  	buttonPanel.add(testSel);
  	//add all checkboxes needed for the Rule testing
  	//TODO: add selction of the Rules to be tested here
	getContentPane().add(buttonPanel);
    }

    public void setSimplifyCount(String s){
	try{
	}catch(NumberFormatException ex){
	    System.out.println(ex);
	    // do nothing
	}
    }
    
    public StringBuffer getLatestTests(){
        return latestTests;
    }
    
    public void setLatestTests(StringBuffer latest){
        latestTests = latest;
    }

    private void createTest(Object[] pms){
	try{
            String test;
	    if(pms == null){
                test=testBuilder.createTestForProof(mediator.getProof());
                latestTests.append(test+" ");
		mediator.testCaseConfirmation(test);
	    }else{
		SetOfProgramMethod pmSet = SetAsListOfProgramMethod.EMPTY_SET;
		for(int i=0; i<pms.length; i++){
		    pmSet = pmSet.add((ProgramMethod) pms[i]);
		}
                test=testBuilder.createTestForProof(
                          mediator.getProof(), pmSet);
                latestTests.append(test+" ");
		mediator.testCaseConfirmation(test);
	    }
	}catch(Exception e){
	    new ExceptionDialog(Main.getInstance(), e);
	}
    }

}
