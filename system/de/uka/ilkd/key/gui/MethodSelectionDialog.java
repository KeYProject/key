// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.unittest.*;
import de.uka.ilkd.key.unittest.simplify.*;
import de.uka.ilkd.key.util.ExtList;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;

import java.awt.event.ActionListener;
import java.awt.event.ActionEvent;
import java.awt.*;
import javax.swing.*;
import javax.swing.border.TitledBorder;

public class MethodSelectionDialog extends JDialog {

    private UnitTestBuilder testBuilder;
    private KeYMediator mediator; 
    private JList methodList;
    private final JCheckBox simplify = new JCheckBox("Simplify");
    private final JCheckBox cogent = new JCheckBox("Cogent");
    private final JCheckBox completeEx = new JCheckBox("Only completely "+
						       "executed traces");
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
	instance.cogent.setSelected(ModelGenerator.decProdForTestGen ==
				    ModelGenerator.COGENT);
	instance.simplify.setSelected(ModelGenerator.decProdForTestGen ==
				      ModelGenerator.SIMPLIFY);
	instance.completeEx.setSelected(UnitTestBuilder.requireCompleteExecution);
	return instance;
    }

    private void layoutMethodSelectionDialog(){
	getContentPane().setLayout(new BoxLayout(getContentPane(), 
						 BoxLayout.Y_AXIS));
	final MethodSelectionDialog thisRef = this;
	final JTextField simplifyDataTupleNumber =
	    new JTextField(""+SimplifyModelGenerator.modelLimit, 2);
	simplifyDataTupleNumber.setToolTipText("Minimal number of data tuples"+
					       "per test method");
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
	    JScrollPane(JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED, 
			JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
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
		    setSimplifyCount(simplifyDataTupleNumber.getText());
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
			setSimplifyCount(simplifyDataTupleNumber.getText());
			createTest(methodList.getSelectedValues());
		    }
		}
	    });
  	buttonPanel.add(testSel);
	simplify.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    if(simplify.isSelected()){
		        ModelGenerator.decProdForTestGen = 
		            ModelGenerator.SIMPLIFY;
                        ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().
                        setDecisionProcedureForTest(DecisionProcedureSettings.SIMPLIFY);  
			buttonPanel.add(simplifyDataTupleNumber, 
					buttonPanel.getComponentCount()-1);
			simplifyDataTupleNumber.setText(
			    ""+SimplifyModelGenerator.modelLimit);
			cogent.setSelected(false);
			thisRef.pack();
		    }else{
			ModelGenerator.decProdForTestGen = 
			    ModelGenerator.COGENT;
                        ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().
                        setDecisionProcedureForTest(DecisionProcedureSettings.COGENT);
			buttonPanel.remove(simplifyDataTupleNumber);
			simplify.setSelected(false);
			cogent.setSelected(true);
			thisRef.pack();
		    }
		}
	    });
	cogent.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    if(cogent.isSelected()){
			ModelGenerator.decProdForTestGen = 
			    ModelGenerator.COGENT;
			buttonPanel.remove(simplifyDataTupleNumber);
			simplify.setSelected(false);
			thisRef.pack();
		    }else{
			ModelGenerator.decProdForTestGen = 
			    ModelGenerator.SIMPLIFY;
			buttonPanel.add(simplifyDataTupleNumber, 
					buttonPanel.getComponentCount()-1);
			simplifyDataTupleNumber.setText(
			    ""+SimplifyModelGenerator.modelLimit);
			cogent.setSelected(false);
			simplify.setSelected(true);
			thisRef.pack();
		    }
		}
	    });
	completeEx.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    UnitTestBuilder.requireCompleteExecution = 
			completeEx.isSelected();
		}
	    });
	JButton exit = new JButton("Exit");
	exit.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    setSimplifyCount(simplifyDataTupleNumber.getText());
		    setVisible(false);
		    dispose();
		    instance = null;
		}
	    });
	buttonPanel.add(completeEx);
	buttonPanel.add(cogent);
	buttonPanel.add(simplify);
	if(ModelGenerator.decProdForTestGen == ModelGenerator.SIMPLIFY){
	    buttonPanel.add(simplifyDataTupleNumber);	    
	}
   	buttonPanel.add(exit);
	getContentPane().add(buttonPanel);
    }

    public void setSimplifyCount(String s){
	try{
	    SimplifyModelGenerator.modelLimit = Integer.parseInt(s);
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
	    ExtList l = new ExtList();
	    l.add(e);
	    new ExceptionDialog(Main.getInstance(), l);
	}
    }

}
