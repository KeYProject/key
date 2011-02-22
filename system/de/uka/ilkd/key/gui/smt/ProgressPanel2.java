package de.uka.ilkd.key.gui.smt;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JProgressBar;
import javax.swing.SwingUtilities;
import javax.swing.border.TitledBorder;

public class ProgressPanel2 extends JPanel{
    
    
    
    
    private JProgressBar bars [];
    
    
    public ProgressPanel2(String name, int numberOfProcesses, int resolution, String [] names){
	assert numberOfProcesses == names.length;
	this.setBorder(BorderFactory.createTitledBorder(null, name,
			TitledBorder.DEFAULT_JUSTIFICATION, TitledBorder.DEFAULT_POSITION,
			new Font("Dialog", Font.BOLD, 12), new Color(51, 51, 51)));    
	this.setLayout(new BoxLayout(this, BoxLayout.X_AXIS));
	this.setBackground(Color.WHITE);
	createProgressBars(numberOfProcesses,resolution, names);

    }
    
    private void createProgressBars(int numberOfBars, int resolution, String [] names){
	bars = new JProgressBar[numberOfBars];
	for(int i=0; i < bars.length; i++){
	    bars[i] = new JProgressBar();
	    bars[i].setMaximumSize(new Dimension(Integer.MAX_VALUE,20));
	    bars[i].setMaximum(resolution);
	    bars[i].setStringPainted(true);
	    
	    this.add(new JLabel(names[i]+": "));
	    this.add(bars[i]);
	    this.add(Box.createHorizontalStrut(10));
	}
    }
    
    public void setProgress(final int processIndex,final int progress){
	if(processIndex >= 0 && processIndex < bars.length){
	    SwingUtilities.invokeLater(new Runnable() {
	        @Override
	        public void run() {
		    bars[processIndex].setValue(progress);
	        }
	    });
	}
    }
    
    public void setColor(final int processIndex, final Color color){
	if(processIndex >= 0 && processIndex < bars.length){
	    SwingUtilities.invokeLater(new Runnable() {
	        @Override
	        public void run() {
	            bars[processIndex].setBackground(color);
	        }
	    });
	
	}
    }
    
    public void setText(final int processIndex,final String text){
	if(processIndex >= 0 && processIndex < bars.length){
	    SwingUtilities.invokeLater(new Runnable() {
	        @Override
	        public void run() {
		    bars[processIndex].setString(text);
	        }
	    });
	}
    }
    
    
    

    
   
    
    
}
