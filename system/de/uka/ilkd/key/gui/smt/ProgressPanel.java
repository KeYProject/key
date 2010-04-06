package de.uka.ilkd.key.gui.smt;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.Graphics;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.Shape;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;


import javax.swing.AbstractButton;
import javax.swing.BorderFactory;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JComponent;

import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JProgressBar;
import javax.swing.SwingUtilities;
import javax.swing.border.TitledBorder;




import de.uka.ilkd.key.gui.ErrorMessages;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.smt.MakesProgress;
import de.uka.ilkd.key.smt.SMTProgressMonitor;
import de.uka.ilkd.key.smt.launcher.Process;



class ProgressPanel implements SMTProgressMonitor {

    	static class InternGoal{
    	    Goal goal;
    	    SolveType type = SolveType.UNKOWN;
    	    public InternGoal(Goal goal){
    		this.goal = goal;
    	    }
    	    
    	}
    
	// The KeY-Colors
	private static final Color PROGRESS_COLOR = new Color(0,153,49);
	private static final Color TIME_COLOR = new Color(0,0,98);
	
	private JProgressBar progressBarTime = null;
	private JLabel jLabel = null;
	private JLabel jLabel1 = null;
	private JPanel progressPanel = null;
	private JProgressBar progressBar = null;
	private JButton progressButton = null;
	private JComponent  parent;
	private ProgressDialog dialog;
	private MakesProgress process;
	
	private List<InternGoal> goals = Collections.synchronizedList(new LinkedList<InternGoal>()); 
	
	
	

	
	
	
	public ProgressPanel(MakesProgress process, JComponent parent, ProgressDialog dialog, Collection<Goal> goals){
	    	this.parent = parent;
	    	this.dialog = dialog;
	    	for(Goal goal : goals){
	    	    this.goals.add(new InternGoal(goal));
	    	}
	    	
	    	
	    	process.removeAllProgressMonitors();
	    	process.addProgressMonitor(this);
	    	
		getProgressBarTime().setMaximum(MAX_TIME);
		getProgressBarTime().setForeground(TIME_COLOR);
		getProgressBar().setForeground(PROGRESS_COLOR);
		getProgressBar().setStringPainted(true);
		getProgressBarTime().setStringPainted(true);
		
		getProgressBar().setString("");
		getProgressBar().setMaximum(goals.size());
		

		((TitledBorder)getComponent().getBorder()).setTitle(process.getTitle());
		this.process = process;
		
	}
	



	
	private String buildString(int progress, int max){
	    return "Goals: "+ progress+"/"+max;
	}
	
	public void setProgress(int progress){
	    	getProgressBar().setString(buildString(progress,getProgressBar().getMaximum()));	    
		getProgressBar().setValue(progress);
		parent.repaint();
		
		//getProgressBar().paint(getProgressBar().getGraphics());
	}
	
	public void setTimeProgress(int progress){
		getProgressBarTime().setValue(progress);
		parent.repaint();
		
	
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
			
			//progressPanel.add(getProgressButton(), gridBagConstraints1);
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
			progressBar = new JProgressBar(){
				@Override
				protected void paintComponent(Graphics g) {
				    int i =0;
				    for(InternGoal goal : goals){
					paintGoal(g,this,i,goal.type);
					i++;
				    }
				    
			    	   
				}  
			};
			
			
			
		}
		return progressBar;
	}
	
	private String goalString(int number, SolveType type){
	    return number+". Goal"+" "+type.name();
	}
	
	public int necessaryPanelWidth(int goals){
	    
	    return SwingUtilities.computeStringWidth(
		    getProgressBar().getFontMetrics(getProgressBar().getFont()), goalString(1,SolveType.UNSOLVABLE))*goals;
	}
	
	public int necessaryPanelHeight(){
	    return getComponent().getHeight();
	}
	
	private void paintGoal(Graphics g,JProgressBar bar,int number,SolveType solved){
	
	    Graphics gc = g.create();
	    
	   if(solved == SolveType.UNKOWN){
	       gc.setColor(bar.getBackground());
	   }else if(solved == SolveType.UNSOLVABLE){
	       gc.setColor(Color.RED);
	   }else {
	       gc.setColor(PROGRESS_COLOR);
	   }
	   
	   int max = bar.getMaximum();
	   int fw = bar.getWidth() / max;
	   
	   String s = goalString(number+1,solved);
	   int width = SwingUtilities.computeStringWidth(g.getFontMetrics(), s);
	
	  
	   
	   
	   gc.fillRect(fw*number, 0, fw, bar.getHeight()); 
	   
	   if(solved == SolveType.UNKOWN){
	       gc.setColor(Color.GRAY);
	   }else if(solved == SolveType.SOLVABLE){
	       gc.setColor(Color.WHITE);
	   }else {
	       gc.setColor(Color.WHITE);
	   }
	   
	  
	   
	   Shape old = gc.getClip();
	   
	   gc.setClip(fw*number+1, 0+1, fw-2,bar.getHeight()-2);

	   gc.drawString(s,fw*number+ (fw-width)/2 , bar.getHeight()-4);
	   gc.setClip(old);
	   gc.drawRect(fw*number, 0, fw, bar.getHeight()); 
	  
	   gc.dispose();
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


        public void setMaximum(int maximum) {
    	    getProgressBar().setString(buildString(getProgressBar().getValue(),maximum));
        }


        public void setTimeMaximum(int maximum) {
            getProgressBarTime().setMaximum(maximum);
	    
        }

        private InternGoal findGoal(Goal goal){
            synchronized(goals){
            for(InternGoal g: goals){
        	if(goal == g.goal){
        	    return g;
        	}
            }
            }
            return null;
        }

        public void setGoalProgress(Goal goal, SolveType type) {
            InternGoal ig = findGoal(goal);
            if(ig != null){
        	ig.type = type;
            }
           parent.repaint();
        }


        public void exceptionOccurred(String s,Exception e) {
            if(!dialog.getStopRunning()){
        	ErrorMessages.showBugMessage(ProgressDialog.INSTANCE, s, e);
            }
            
            
	    
        }

        private int countSolveType(List<InternGoal> goals, SolveType type){
            int counter =0;
            for(InternGoal goal : goals){
        	if(goal.type == type){
        	    counter++;
        	}
            }
            return counter;
        }
	
        public void setSolverFinished(long time) {
            getProgressBarTime().setString("Stoped after "+ ((double)time)/1000 + " sec.");
            parent.repaint();
            int count, solved;
           
            synchronized(dialog){
       	 	synchronized (goals) {
       	 	    count = goals.size();
       	 	    solved = countSolveType(goals,SolveType.SOLVABLE);
                }
       	 	System.out.println(process.getTitle());
        	dialog.processHasFinished(this, count, solved);
        
            }
        }
}
