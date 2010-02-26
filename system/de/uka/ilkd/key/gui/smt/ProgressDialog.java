package gui;



import javax.swing.JPanel;

import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.GridBagLayout;
import java.awt.Dimension;
import javax.swing.BorderFactory;
import javax.swing.border.TitledBorder;
import java.awt.Font;
import java.awt.Color;
import javax.swing.JProgressBar;
import java.awt.GridBagConstraints;
import javax.swing.JButton;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;

import javax.swing.DefaultListCellRenderer;
import javax.swing.DefaultListModel;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JList;
import javax.swing.JLabel;
import javax.swing.JScrollPane;
import javax.swing.ListCellRenderer;
import javax.swing.ListModel;

public class ProgressDialog extends JFrame{

	

	private JPanel panelDialog = null;  //  @jve:decl-index=0:visual-constraint="498,19"
	private JList list = null;
	private JPanel buttonPanel = null;
	private JButton okButton = null;
	private JButton cancelButton = null;
	private JScrollPane scrollPane = null;

	
	public void setProgress(int i, int progress){
		ProgressPanel panel = (ProgressPanel)list.getModel().getElementAt(i);
		panel.setProgress(progress);
		getList().repaint();
	}
	
	
	
	ProgressDialog(){
		setLayout(new BorderLayout());
		getCancelButton().addActionListener(new ActionListener(){

			@Override
			public void actionPerformed(ActionEvent e) {
				System.exit(0);
				
			}
			
		});
		getList().setCellRenderer(new ListCellRenderer(){

			@Override
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
	
	void showDialog(ListModel model){
		getList().setModel(model);
		this.setSize(300, 300);
		this.setVisible(true);
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
			gridBagConstraints3.gridy = 1;
			GridBagConstraints gridBagConstraints2 = new GridBagConstraints();
			gridBagConstraints2.fill = GridBagConstraints.BOTH;
			gridBagConstraints2.gridy = 0;
			gridBagConstraints2.weightx = 1.0;
			gridBagConstraints2.weighty = 1.0;
			gridBagConstraints2.gridx = 0;
			panelDialog = new JPanel();
			panelDialog.setLayout(new GridBagLayout());
			panelDialog.setSize(new Dimension(300, 195));
			panelDialog.add(getScrollPane(), gridBagConstraints2);
			panelDialog.add(getButtonPanel(), gridBagConstraints3);
		}
		return panelDialog;
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
			buttonPanel.add(getOkButton(), gridBagConstraints4);
			buttonPanel.add(getCancelButton(), gridBagConstraints5);
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
			okButton.setText("OK");
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
			cancelButton.setText("Cancel");
		}
		return cancelButton;
	}



}
