package gui;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;

import javax.swing.AbstractButton;
import javax.swing.BorderFactory;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JProgressBar;
import javax.swing.border.TitledBorder;
import javax.swing.plaf.ProgressBarUI;

import sun.font.CreatedFontTracker;

public class ProgressPanel {

	// The KeY-Colors
	private static final Color PROGRESS_COLOR = new Color(0,153,49);
	private static final Color TIME_COLOR = new Color(0,0,98);
	public static final ImageIcon ICON_CANCEL = createImageIcon("cancel.jpg");
	public static final ImageIcon ICON_UNKNOWN = createImageIcon("unknown.jpg");
	public static final ImageIcon ICON_SOLVABLE = createImageIcon("solvable.jpg");
	public static final ImageIcon ICON_NOT_SOLVABLE = createImageIcon("unsolvable.jpg");
	
	private JProgressBar progressBarTime = null;
	private JLabel jLabel = null;
	private JLabel jLabel1 = null;
	private JPanel progressPanel = null;
	private JProgressBar progressBar = null;
	private JButton progressButton = null;
	private Object  userObject=null;
	
	
	
	public ProgressPanel(String title,Object user){
		userObject = user;
		getProgressBarTime().setMaximum(1000);
		getProgressBar().setMaximum(1000);
		getProgressBarTime().setForeground(TIME_COLOR);
		getProgressBar().setForeground(PROGRESS_COLOR);
		getProgressBar().setValue(100);
		
		
		
		getProgressButton().setIcon(ICON_UNKNOWN);
		((TitledBorder)getComponent().getBorder()).setTitle(title);
		
	}
	
	private static ImageIcon createImageIcon(String path) {
		java.net.URL imgURL = ProgressPanel.class.getResource(path);
		if (imgURL != null) {
			ImageIcon icon = new ImageIcon(imgURL);
			return icon;
		} else {
			System.err.println("Couldn't find file: " + path);
			return null;
		}
	}

	
	public void setResultIcon(ImageIcon icon){
		getProgressButton().setIcon(icon);
		
	}
	
	public void setProgress(int progress){
		getProgressBar().setValue(progress);
		
		//getProgressBar().paint(getProgressBar().getGraphics());
	}
	
	public void setTimeProgress(int progress){
		getProgressBarTime().setValue(progress);
		
	
	}
	
	/**
	 * This method initializes progressPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	public JPanel getComponent() {
		if (progressPanel == null) {
			GridBagConstraints gridBagConstraints8 = new GridBagConstraints();
			gridBagConstraints8.gridx = 0;
			gridBagConstraints8.weighty = 1.0;
			gridBagConstraints8.anchor = GridBagConstraints.NORTHWEST;
			gridBagConstraints8.gridy = 1;
			jLabel1 = new JLabel();
			jLabel1.setText("Time:");
			GridBagConstraints gridBagConstraints7 = new GridBagConstraints();
			gridBagConstraints7.gridx = 0;
			gridBagConstraints7.weighty = 1.0;
			gridBagConstraints7.insets = new Insets(0, 0, 5, 0);
			gridBagConstraints7.anchor = GridBagConstraints.NORTHWEST;
			gridBagConstraints7.gridy = 0;
			jLabel = new JLabel();
			jLabel.setText("Progress: ");
			GridBagConstraints gridBagConstraints6 = new GridBagConstraints();
			gridBagConstraints6.gridx = 1;
			gridBagConstraints6.fill = GridBagConstraints.HORIZONTAL;
			gridBagConstraints6.anchor = GridBagConstraints.NORTHWEST;
			gridBagConstraints6.weighty = 1.0;
			gridBagConstraints6.gridy = 1;
			GridBagConstraints gridBagConstraints1 = new GridBagConstraints();
			gridBagConstraints1.gridx = 2;
			gridBagConstraints1.anchor = GridBagConstraints.NORTHWEST;
			gridBagConstraints1.weightx = 0.05;
			gridBagConstraints1.insets = new Insets(0, 10, 0, 0);
			gridBagConstraints1.gridheight = 2;
			gridBagConstraints1.ipady = 0;
			gridBagConstraints1.weighty = 1.0;
			gridBagConstraints1.gridwidth = 1;
			gridBagConstraints1.gridy = 0;
			GridBagConstraints gridBagConstraints = new GridBagConstraints();
			gridBagConstraints.gridx = 1;
			gridBagConstraints.anchor = GridBagConstraints.NORTHWEST;
			gridBagConstraints.ipadx = 0;
			gridBagConstraints.insets = new Insets(0, 0, 5, 0);
			gridBagConstraints.weightx = 1.0;
			gridBagConstraints.fill = GridBagConstraints.HORIZONTAL;
			gridBagConstraints.weighty = 1.0;
			gridBagConstraints.gridy = 0;
			progressPanel = new JPanel();
			progressPanel.setLayout(new GridBagLayout());
			progressPanel.setSize(new Dimension(353, 63));
			progressPanel.setBorder(BorderFactory.createTitledBorder(null, "ProgressPanel", TitledBorder.DEFAULT_JUSTIFICATION, TitledBorder.DEFAULT_POSITION, new Font("Dialog", Font.BOLD, 12), new Color(51, 51, 51)));
			progressPanel.add(getProgressBar(), gridBagConstraints);
			
			progressPanel.add(getProgressButton(), gridBagConstraints1);
			progressPanel.add(getProgressBarTime(), gridBagConstraints6);
			progressPanel.add(jLabel, gridBagConstraints7);
			progressPanel.add(jLabel1, gridBagConstraints8);
		}
		return progressPanel;
	}
	
	/**
	 * This method initializes progressBar	
	 * 	
	 * @return javax.swing.JProgressBar	
	 */
	private JProgressBar getProgressBar() {
		if (progressBar == null) {
			progressBar = new JProgressBar();
		}
		return progressBar;
	}

	/**
	 * This method initializes progressButton	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getProgressButton() {
		if (progressButton == null) {
			progressButton = new JButton();
			progressButton.setBackground(Color.WHITE);
			progressButton.setMargin(new Insets(0,0,0,0));
			progressButton.setVerticalAlignment(AbstractButton.CENTER);
			progressButton.setMaximumSize(new Dimension(30,30));
			progressButton.setMinimumSize(new Dimension(30,30));
			progressButton.setPreferredSize(new Dimension(30,30));
		}
		return progressButton;
	}
	
	/**
	 * This method initializes progressBarTime	
	 * 	
	 * @return javax.swing.JProgressBar	
	 */
	private JProgressBar getProgressBarTime() {
		if (progressBarTime == null) {
			progressBarTime = new JProgressBar();
		
		}
		return progressBarTime;
	}
}
