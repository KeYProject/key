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
import javax.swing.JComboBox;
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
import de.uka.ilkd.key.unittest.simplify.SimplifyModelGenerator;

public class MethodSelectionDialog extends JDialog {

    private UnitTestBuilder testBuilder;

    private KeYMediator mediator;

    JList methodList;

    final static String OLD_SIMPLIFY = "Simplify (old interface)";

    final static String SIMPLIFY = "Simplify (new interface)";

    final static String COGENT = "Cogent";

    JComboBox solverChoice = new JComboBox(new String[] { OLD_SIMPLIFY,
	    SIMPLIFY, COGENT });

    final JCheckBox completeEx = new JCheckBox("Only completely "
	    + "executed traces");

    final JTextField simplifyDataTupleNumber;

    static MethodSelectionDialog instance = null;

    private StringBuffer latestTests = new StringBuffer();

    private MethodSelectionDialog(KeYMediator mediator) {
	super(mediator.mainFrame(), "Method selection dialog");
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

	switch (ModelGenerator.decProdForTestGen) {
	case ModelGenerator.OLD_SIMPLIFY:
	    instance.solverChoice.setSelectedItem(OLD_SIMPLIFY);
	    break;
	case ModelGenerator.SIMPLIFY:
	    instance.solverChoice.setSelectedItem(SIMPLIFY);
	    break;
	case ModelGenerator.COGENT:
	    instance.solverChoice.setSelectedItem(COGENT);
	    break;
	default:
	    throw new RuntimeException(
		    "Unhandled case in MethodSelecitonDialog.");
	}
	instance.completeEx
		.setSelected(UnitTestBuilder.requireCompleteExecution);
	instance.simplifyDataTupleNumber.setText(Integer
		.toString(SimplifyModelGenerator.modelLimit));
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
	} catch (NumberFormatException ex) {
	    System.out.println(ex);
	    // do nothing
	}
    }

    private boolean layoutWasCalled = false;

    private void layoutMethodSelectionDialog() {
	if (layoutWasCalled)
	    throw new RuntimeException(
		    "Method  \"layoutMethodSelectionDialog\" must not be called multiple times.");
	layoutWasCalled = true;
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

	solverChoice.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
		if (e.getSource() != solverChoice)
		    throw new RuntimeException(
			    "CodeError: ActionListener is used by wrong combobox.");
		if (solverChoice.getSelectedItem() == OLD_SIMPLIFY) {
		    ModelGenerator.decProdForTestGen = ModelGenerator.OLD_SIMPLIFY;
		} else if (solverChoice.getSelectedItem() == SIMPLIFY) {
		    ModelGenerator.decProdForTestGen = ModelGenerator.SIMPLIFY;
		} else if (solverChoice.getSelectedItem() == COGENT) {
		    ModelGenerator.decProdForTestGen = ModelGenerator.COGENT;
		} else {
		    throw new RuntimeException(
			    "Not implemented case in MethodSelectionDialog");
		}
		simplifyDataTupleNumber.setEnabled(solverChoice
			.getSelectedItem() == OLD_SIMPLIFY
			|| solverChoice.getSelectedItem() == SIMPLIFY);
	    }
	});
	buttonPanel.add(solverChoice);

	buttonPanel.add(simplifyDataTupleNumber);

	simplifyDataTupleNumber
		.setEnabled(solverChoice.getSelectedItem() == OLD_SIMPLIFY
			|| solverChoice.getSelectedItem() == SIMPLIFY);
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