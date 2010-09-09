// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.gui.smt;


import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.util.Collection;

import javax.swing.DefaultListModel;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.ListCellRenderer;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.smt.SMTRule;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.launcher.ProcessLauncherListener;


public class SMTProgressDialog extends JDialog implements ProcessLauncherListener {
    private static final long serialVersionUID = 1L;

    public static final SMTProgressDialog INSTANCE = new SMTProgressDialog();


    private JPanel panelDialog = null;  //  @jve:decl-index=0:visual-constraint="498,19"
    private JList list = null;
    private JPanel buttonPanel = null;
    private JButton okButton = null;
    private JButton cancelButton = null;
    private JButton stopButton = null;
    private JScrollPane scrollPane = null;
    private JTextArea   infoText = null;
    private SMTRule rule = null;
    private int numberOfProcesses =0;
    private boolean stopRunning = false;
    private boolean applyResults = false;

	
    public void prepare(Collection<SMTSolver> solvers, Collection<Goal> goals, SMTRule r){
	this.rule = r;
	rule.addListener(this);
	int width=0;
	int height =0;
	DefaultListModel model = new DefaultListModel();
	numberOfProcesses = 0;
	getList().setModel(model);
	getStopButton().setEnabled(true);
	for(SMTSolver solver : solvers){
	    ProgressPanel panel =new ProgressPanel(solver,getList(),this,goals); 
	    model.addElement(panel);
	    width = Math.max(width, panel.necessaryPanelWidth(goals.size()));
	    height += panel.necessaryPanelHeight();
	    numberOfProcesses++;
	}

	height += getInfoText().getPreferredSize().height+10;
	stopRunning = false;


	width += 120;
	height += 100;
	Dimension dim = Toolkit.getDefaultToolkit().getScreenSize();
	width = Math.max(500, Math.min(width, dim.width*3/4));
	height = Math.min(height,dim.height/2);

	this.setSize(width,height);
    }
	
	
	
    private SMTProgressDialog(){
	setSize(500, 200);
	setLocationByPlatform(true);

	this.setDefaultCloseOperation(DO_NOTHING_ON_CLOSE);

	setLayout(new BorderLayout());
	setTitle("Progress of SMT solvers");


	getList().setCellRenderer(new ListCellRenderer(){


	    public Component getListCellRendererComponent(JList arg0,
		    Object object, int arg2, boolean arg3, boolean arg4) {
		return ((ProgressPanel)object).getComponent();
	    }

	});


	this.getContentPane().add(getPanelDialog(),BorderLayout.CENTER);
    }

    void paintDialog(){
	this.repaint();
    }

    public void showDialog(){
        if (SMTSettings.getInstance().getProgressDialogMode() == 
            SMTSettings.PROGRESS_MODE_USER) {
	    getCancelButton().setEnabled(true);
	    getOkButton().setEnabled(true);
        } else {
	    getCancelButton().setEnabled(false);
	    getOkButton().setEnabled(false);
        }
	setVisible(true);

    }

    public void setVisible(boolean b){
	this.setModal(b);
	//getOkButton().setEnabled(false);
	super.setVisible(b);
    }


    public boolean getStopRunning(){
	return stopRunning;
    }



    /**
     * This method initializes panelDialog	
     * 	
     * @return javax.swing.JPanel	
     */
    private JPanel getPanelDialog() {
	if (panelDialog == null) {
	    GridBagConstraints gridBagConstraints3 = new GridBagConstraints();
	    gridBagConstraints3.gridx = 0;
	    gridBagConstraints3.weighty = 0.0;
	    gridBagConstraints3.fill = GridBagConstraints.BOTH;
	    gridBagConstraints3.weightx = 1.0;
	    gridBagConstraints3.ipadx = 0;
	    gridBagConstraints3.insets = new Insets(5, 0, 5, 0);
	    gridBagConstraints3.gridy = 2;
	    GridBagConstraints gridBagConstraints2 = new GridBagConstraints();
	    gridBagConstraints2.fill = GridBagConstraints.BOTH;
	    gridBagConstraints2.gridy = 0;
	    gridBagConstraints2.weightx = 1.0;
	    gridBagConstraints2.weighty = 1.0;
	    gridBagConstraints2.gridx = 0;

	    GridBagConstraints gridBagConstraints4 = new GridBagConstraints();
	    gridBagConstraints4.gridx = 0;
	    gridBagConstraints4.weighty = 0.0;
	    gridBagConstraints4.fill = GridBagConstraints.BOTH;
	    gridBagConstraints4.weightx = 1.0;
	    gridBagConstraints4.ipadx = 0;
	    gridBagConstraints4.insets = new Insets(5, 5, 5, 5);
	    gridBagConstraints4.gridy = 1;

	    panelDialog = new JPanel();
	    panelDialog.setLayout(new GridBagLayout());
	    panelDialog.setSize(new Dimension(300, 195));
	    panelDialog.add(getScrollPane(), gridBagConstraints2);
	    panelDialog.add(getInfoText(),gridBagConstraints4);
	    panelDialog.add(getButtonPanel(), gridBagConstraints3);
	    getInfoText().setBackground(panelDialog.getBackground());
	}
	return panelDialog;
    }


    private JTextArea getInfoText(){
	if(infoText == null){
	    infoText = new JTextArea();
	    infoText.setEditable(false);
	    infoText.setRows(2);
	    infoText.setText("You can change the behavior of this dialog via Options/SMT Solvers");
	}
	return infoText;
    }


    private JScrollPane getScrollPane(){
	if (scrollPane == null) {
	    scrollPane = new JScrollPane(getList());

	}
	return scrollPane;
    }

    /**
     * This method initializes list	
     * 	
     * @return javax.swing.JList	
     */
    private JList getList() {
	if (list == null) {
	    list = new JList();

	}
	return list;
    }

    /**
     * This method initializes buttonPanel	
     * 	
     * @return javax.swing.JPanel	
     */
    private JPanel getButtonPanel() {
	if (buttonPanel == null) {
	    GridBagConstraints gridBagConstraints3 = new GridBagConstraints();
	    gridBagConstraints3.gridx = 2;
	    gridBagConstraints3.insets = new Insets(0, 0, 0, 5);
	    gridBagConstraints3.anchor = GridBagConstraints.EAST;
	    gridBagConstraints3.weightx = 0.1;
	    gridBagConstraints3.gridy = 0;
	    GridBagConstraints gridBagConstraints5 = new GridBagConstraints();
	    gridBagConstraints5.gridx = 1;
	    gridBagConstraints5.insets = new Insets(0, 0, 0, 5);
	    gridBagConstraints5.anchor = GridBagConstraints.EAST;
	    gridBagConstraints5.weightx = 0.1;
	    gridBagConstraints5.gridy = 0;
	    GridBagConstraints gridBagConstraints4 = new GridBagConstraints();
	    gridBagConstraints4.gridx = 0;
	    gridBagConstraints4.weightx = 1.0;
	    gridBagConstraints4.anchor = GridBagConstraints.EAST;
	    gridBagConstraints4.gridwidth = 1;
	    gridBagConstraints4.ipadx = 0;
	    gridBagConstraints4.gridy = 0;
	    buttonPanel = new JPanel();
	    buttonPanel.setLayout(new GridBagLayout());
	    buttonPanel.setForeground(Color.green);
	    buttonPanel.add(getStopButton(),gridBagConstraints3);
	    buttonPanel.add(getCancelButton(), gridBagConstraints4);
	    buttonPanel.add(getOkButton(), gridBagConstraints5);
	}
	return buttonPanel;
    }

    /**
     * This method initializes okButton	
     * 	
     * @return javax.swing.JButton	
     */
    private JButton getOkButton() {
	if (okButton == null) {
	    okButton = new JButton();
	    okButton.setText("Apply Results");
	    okButton.addActionListener(new ActionListener() {

		public void actionPerformed(ActionEvent arg0) {
		    applyAndClose();

		}
	    });

	}
	return okButton;
    }

    /**
     * This method initializes cancelButton	
     * 	
     * @return javax.swing.JButton	
     */
    private JButton getCancelButton() {
	if (cancelButton == null) {
	    cancelButton = new JButton();
	    cancelButton.setText("Discard Results");
	    cancelButton.addActionListener(new ActionListener() {

		public void actionPerformed(ActionEvent e) {
		    setVisible(false);
		    stopRunning = true;
		    rule.stop();

		}
	    });
	}
	return cancelButton;
    }

    private JButton getStopButton() {
	if (stopButton == null) {
	    stopButton = new JButton();
	    stopButton.setText("Stop");
	    stopButton.setIcon(IconFactory.autoModeStopLogo(15));
	    stopButton.addActionListener(new ActionListener() {

		public void actionPerformed(ActionEvent e) {
		    stopRunning = true;
		    rule.stop();
                    int mode = SMTSettings.getInstance().
                        getProgressDialogMode();
	            if ((mode == SMTSettings.PROGRESS_MODE_CLOSE ||
		            mode == SMTSettings.PROGRESS_MODE_CLOSE_FIRST)){
	                setVisible(false);
                    }
		}
	    });
	}
	return stopButton;
    }

    private void applyAndClose(){
	stopRunning = true;
	setVisible(false);	
	rule.stop();	    	
	rule.applyResults();
    }



    // This method is called by the Boss-Thread of the SMTRule. 
    // Because it is important to apply the results in the AWT-Thread, 
    // the following mechanism is introduced.
    public void workDone() {
	getStopButton().setEnabled(false);
        applyResults = true;
	int mode = SMTSettings.getInstance().getProgressDialogMode();
	if((mode == SMTSettings.PROGRESS_MODE_CLOSE ||
		mode == SMTSettings.PROGRESS_MODE_CLOSE_FIRST)){
            KeYMediator.invokeAndWait(new Runnable() {
                public void run() {applyAndClose();}
            });

	}
	repaint();
    }
}
