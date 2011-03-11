package de.uka.ilkd.key.gui.smt;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Collection;
import java.util.LinkedList;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JProgressBar;
import javax.swing.SwingUtilities;
import javax.swing.border.TitledBorder;
import javax.swing.plaf.basic.BasicProgressBarUI;

import de.uka.ilkd.key.gui.smt.InformationWindow.Information;

public class ProgressPanel extends JPanel{
    

    private static final long serialVersionUID = 1L;

    private static class SingleProgressPanel extends JPanel{
        private static final long serialVersionUID = 1L;
	final JProgressBar bar = new JProgressBar();
	final JButton      button = new JButton();
	final Collection<Information> information = new LinkedList<Information>();
	SingleProgressPanel(String name, int resolution){
	
	    this.setBackground(Color.WHITE);
	    this.setLayout(new BoxLayout(this, BoxLayout.X_AXIS));
	    bar.setMaximumSize(new Dimension(Integer.MAX_VALUE,20));
	    bar.setMaximum(resolution);
	    bar.setStringPainted(true);
	    
	
	    button.addActionListener(new ActionListener() {
	        
	        @Override
	        public void actionPerformed(ActionEvent e) {
	            new InformationWindow(information);
	        }
	    });
	    button.setText("i");
	    button.setMaximumSize(new Dimension(20,20));
	    button.setEnabled(false);
	    
	    this.add(new JLabel(name+": "));
	    this.add(bar);
	    this.add(Box.createHorizontalStrut(2));
	    this.add(button);
	}
    }
    
    
    private SingleProgressPanel bars [];
    
    
    public ProgressPanel(String name, int numberOfProcesses, int resolution, String [] names){
	assert numberOfProcesses == names.length;
	this.setBorder(BorderFactory.createTitledBorder(null, name,
			TitledBorder.DEFAULT_JUSTIFICATION, TitledBorder.DEFAULT_POSITION,
			new Font("Dialog", Font.BOLD, 12), new Color(51, 51, 51)));    
	this.setLayout(new BoxLayout(this, BoxLayout.X_AXIS));
	this.setBackground(Color.WHITE);
	createProgressBars(numberOfProcesses,resolution, names);

    }
    
    private void createProgressBars(int numberOfBars, int resolution, String [] names){
	bars = new SingleProgressPanel[numberOfBars];
	
	for(int i=0; i < bars.length; i++){
	    bars[i] = new SingleProgressPanel(names[i], resolution);
	    this.add(bars[i]);
	    this.add(Box.createHorizontalStrut(10));
	}
    }
    
    public void setProgress(final int processIndex,final int progress){
	if(processIndex >= 0 && processIndex < bars.length){
	    SwingUtilities.invokeLater(new Runnable() {
	        @Override
	        public void run() {
		    bars[processIndex].bar.setValue(progress);
	        }
	    });
	}
    }
    
    public void setColor(final int processIndex, final Color color){
	if(processIndex >= 0 && processIndex < bars.length){
	    SwingUtilities.invokeLater(new Runnable() {
	        @Override
	        public void run() {
	            
	          //  bars[processIndex].setBackground(color);
	            
	            bars[processIndex].bar.setUI(  new BasicProgressBarUI() {
	        	protected Color getSelectionBackground() { return color; }
	            });
	            	
	        }
	    });
	
	}
    }
    
    public void addInformation(int processIndex,Information info){
	bars[processIndex].information.add(info);
	bars[processIndex].button.setEnabled(true);
    }
    
    public void setText(final int processIndex,final String text){
	if(processIndex >= 0 && processIndex < bars.length){
	    SwingUtilities.invokeLater(new Runnable() {
	        @Override
	        public void run() {
		    bars[processIndex].bar.setString(text);
	        }
	    });
	}
    }
    
    
    

    
   
    
    
}
