// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.gui;

import java.awt.Component;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.BoxLayout;
import javax.swing.DefaultListCellRenderer;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JDialog;
import javax.swing.JList;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextField;
import javax.swing.ScrollPaneConstants;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.SetAsListOfProgramMethod;
import de.uka.ilkd.key.logic.op.SetOfProgramMethod;
import de.uka.ilkd.key.unittest.ModelGenerator;
import de.uka.ilkd.key.unittest.UnitTestBuilder;
import de.uka.ilkd.key.unittest.simplify.OldSimplifyModelGenerator;
import de.uka.ilkd.key.unittest.simplify.SimplifyModelGenerator;

public class MethodSelectionDialog extends JDialog {

    class Al implements ActionListener {

	public void actionPerformed(ActionEvent e) {
	    if (e.getSource().equals(cogent)) {
		ModelGenerator.decProdForTestGen = ModelGenerator.COGENT;
		cogent.setSelected(true);
		simplify.setSelected(false);
		oldSimplify.setSelected(false);
	    } else if (e.getSource().equals(simplify)) {
		ModelGenerator.decProdForTestGen = ModelGenerator.SIMPLIFY;
		cogent.setSelected(false);
		simplify.setSelected(true);
		oldSimplify.setSelected(false);
	    } else if (e.getSource().equals(oldSimplify)) {
		ModelGenerator.decProdForTestGen = ModelGenerator.OLD_SIMPLIFY;
		cogent.setSelected(false);
		simplify.setSelected(false);
		oldSimplify.setSelected(true);
	    }
	    simplifyDataTupleNumber.setEnabled(simplify.isSelected()
		    || oldSimplify.isSelected());
	}
    }

    private UnitTestBuilder testBuilder;

    private KeYMediator mediator;

    JList methodList;

    private ActionListener actLi = new Al();

    final JCheckBox simplify = new JCheckBox("Simplify");

    final JCheckBox oldSimplify = new JCheckBox("Simplify(old)");

    final JCheckBox cogent = new JCheckBox("Cogent");

    final JCheckBox completeEx = new JCheckBox("Only completely "
	    + "executed traces");

    final JTextField simplifyDataTupleNumber;

    static MethodSelectionDialog instance = null;

    private StringBuffer latestTests = new StringBuffer();

    private MethodSelectionDialog(KeYMediator mediator) {
	this.mediator = mediator;
	testBuilder = new UnitTestBuilder(mediator.getServices(), mediator
		.getProof());
	simplifyDataTupleNumber = new JTextField(""
		+ SimplifyModelGenerator.modelLimit, 2);
	layoutMethodSelectionDialog();
	pack();
	setLocation(70, 70);
	setVisible(true);
    }

    public static MethodSelectionDialog getInstance(KeYMediator mediator) {
	if (instance != null) {
	    instance.setVisible(false);
	    instance.dispose();
	}
	instance = new MethodSelectionDialog(mediator);
	instance.cogent
		.setSelected(ModelGenerator.decProdForTestGen == ModelGenerator.COGENT);
	instance.simplify
		.setSelected(ModelGenerator.decProdForTestGen == ModelGenerator.SIMPLIFY);
	instance.oldSimplify
		.setSelected(ModelGenerator.decProdForTestGen == ModelGenerator.OLD_SIMPLIFY);
	instance.completeEx
		.setSelected(UnitTestBuilder.requireCompleteExecution);
	instance.simplifyDataTupleNumber.setText(Integer
		.toString(SimplifyModelGenerator.modelLimit));
	instance.simplifyDataTupleNumber.setText(Integer
		.toString(OldSimplifyModelGenerator.modelLimit));
	return instance;
    }

    public StringBuffer getLatestTests() {
	return latestTests;
    }

    public void setLatestTests(StringBuffer latest) {
	latestTests = latest;
    }

    public void setSimplifyCount(String s) {
	try {
	    SimplifyModelGenerator.modelLimit = Integer.parseInt(s);
	    OldSimplifyModelGenerator.modelLimit = Integer.parseInt(s);
	} catch (NumberFormatException ex) {
	    System.out.println(ex);
	    // do nothing
	}
    }

    private void layoutMethodSelectionDialog() {
	getContentPane().setLayout(
		new BoxLayout(getContentPane(), BoxLayout.Y_AXIS));

	simplifyDataTupleNumber.setToolTipText("Minimal number of data tuples "
		+ "per test method");
	// methodlist
	methodList = new JList();
	methodList.setCellRenderer(new DefaultListCellRenderer() {
	    @Override
	    public Component getListCellRendererComponent(JList list,
		    Object value, int index, boolean isSelected,
		    boolean cellHasFocus) {
		if (value != null) {
		    ProgramMethod pm = (ProgramMethod) value;
		    MethodDeclaration md = pm.getMethodDeclaration();
		    String params = md.getParameters().toString();
		    setText((md.getTypeReference() == null ? "void" : md
			    .getTypeReference().getName())
			    + " "
			    + md.getFullName()
			    + "("
			    + params.substring(1, params.length() - 1) + ")");
		    if (isSelected) {
			setBackground(list.getSelectionBackground());
			setForeground(list.getSelectionForeground());
		    } else {
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
	SetOfProgramMethod pms = testBuilder.getProgramMethods(mediator
		.getProof());
	methodList.setListData(pms.toArray());
	JScrollPane methodListScroll = new JScrollPane(
		ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED,
		ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
	methodListScroll.getViewport().setView(methodList);
	methodListScroll
		.setBorder(new TitledBorder("Methods occuring in Proof"));
	methodListScroll.setMinimumSize(new java.awt.Dimension(250, 400));
	getContentPane().add(methodListScroll);

	// buttons
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
		if (methodList.getSelectedValues().length == 0) {
		    JOptionPane.showMessageDialog(null,
			    "Please select the method(s) first!",
			    "No Methods Selected", JOptionPane.ERROR_MESSAGE);
		} else {
		    setSimplifyCount(simplifyDataTupleNumber.getText());
		    createTest(methodList.getSelectedValues());
		}
	    }
	});
	buttonPanel.add(testSel);

	simplify.addActionListener(actLi);
	cogent.addActionListener(actLi);
	oldSimplify.addActionListener(actLi);

	completeEx.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
		UnitTestBuilder.requireCompleteExecution = completeEx
			.isSelected();
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
	buttonPanel.add(oldSimplify);

	buttonPanel.add(simplifyDataTupleNumber);
	simplifyDataTupleNumber.setEnabled(simplify.isSelected()
		|| oldSimplify.isSelected());
	buttonPanel.add(exit);
	getContentPane().add(buttonPanel);
    }

    void createTest(Object[] pms) {
	try {
	    String test;
	    if (pms == null) {
		test = testBuilder.createTestForProof(mediator.getProof());
		latestTests.append(test + " ");
		mediator.testCaseConfirmation(test);
	    } else {
		SetOfProgramMethod pmSet = SetAsListOfProgramMethod.EMPTY_SET;
		for (int i = 0; i < pms.length; i++) {
		    pmSet = pmSet.add((ProgramMethod) pms[i]);
		}
		test = testBuilder.createTestForProof(mediator.getProof(),
			pmSet);
		latestTests.append(test + " ");
		mediator.testCaseConfirmation(test);
	    }
	} catch (Exception e) {
	    new ExceptionDialog(Main.getInstance(), e);
	}
    }

}
