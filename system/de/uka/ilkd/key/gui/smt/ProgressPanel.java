//package de.uka.ilkd.key.gui.smt;
//
//import java.awt.Color;
//import java.awt.Dimension;
//import java.awt.Font;
//import java.awt.Graphics;
//import java.awt.Graphics2D;
//import java.awt.GridBagConstraints;
//import java.awt.GridBagLayout;
//import java.awt.Insets;
//import java.awt.RenderingHints;
//import java.awt.Shape;
//import java.util.Collection;
//import java.util.Collections;
//import java.util.LinkedList;
//import java.util.List;
//
//
//import javax.swing.BorderFactory;
//import javax.swing.JComponent;
//
//import javax.swing.JLabel;
//import javax.swing.JPanel;
//import javax.swing.JProgressBar;
//import javax.swing.SwingUtilities;
//import javax.swing.border.TitledBorder;
//
//import de.uka.ilkd.key.proof.Goal;
//import de.uka.ilkd.key.smt.MakesProgress;
//import de.uka.ilkd.key.smt.SMTProgressMonitor;
//
//
//
//class ProgressPanel implements SMTProgressMonitor {
//
//    	static class InternGoal{
//    	    Goal goal;
//    	    int index;
//    	    SolveType type = SolveType.UNKOWN;
//    	    public InternGoal(Goal goal,int index){
//    		this.goal = goal;
//    		this.index = index;
//    	    }
//    	    
//    	}
//    
//	// The KeY-Colors
//	private static final Color SOLVED_COLOR = new Color(0,153,49);
//	private static final Color TIME_COLOR = new Color(0,0,98);
//	private static final Color UNKOWN_COLOR = Color.GRAY;
//	private static final Color UNSOLVED_COLOR = new Color(200,0,0);
//	
//	
//	
//	private JProgressBar progressBarTime = null;
//	private JLabel jLabel = null;
//	private JLabel jLabel1 = null;
//	private JPanel progressPanel = null;
//	private JProgressBar progressBar = null;
//	private JComponent  parent;
//	private ProgressDialog dialog;
//	
//	private List<InternGoal> goals = Collections.synchronizedList(new LinkedList<InternGoal>()); 
//	private int currentGoal =0;
//	private long time = System.currentTimeMillis();
//	private int dots =0;
//	private MakesProgress process;
//	
//	
//
//	
//	
//	
//	public ProgressPanel(MakesProgress process, JComponent parent, ProgressDialog dialog, Collection<Goal> goals){
//	    	this.parent = parent;
//	    	this.dialog = dialog;
//	    	this.process = process;
//	    	int i=0;
//	    	for(Goal goal : goals){
//	    	    this.goals.add(new InternGoal(goal,i));
//	    	    i++;
//	    	}
//	    	
//	    	    	
//	    	
//	    	process.removeAllProgressMonitors();
//	    	process.addProgressMonitor(this);
//	    	
//		getProgressBarTime().setMaximum(MAX_TIME);
//		getProgressBarTime().setForeground(TIME_COLOR);
//		getProgressBar().setForeground(SOLVED_COLOR);
//		getProgressBar().setStringPainted(true);
//		getProgressBarTime().setStringPainted(true);
//		setTimeProgress("", 0);
//		
//		getProgressBar().setString("");
//		getProgressBar().setMaximum(goals.size());
//		
//
//		((TitledBorder)getComponent().getBorder()).setTitle(process.getTitle());
//	}
//	
//	String [] s = {"   ",".  ",".. ","..."};
//
//	private String getDotString(){
//	    if(System.currentTimeMillis()-time > 500){
//		dots++;
//		if(dots == s.length){
//		    dots=0;
//		}
//		time = System.currentTimeMillis();
//	    }
//	    return s[dots];
//	    
//	}
//
//	
//	private String buildString(int progress, int max){
//	    return "Goals: "+ progress+"/"+max;
//	}
//	
//	
//	public void setTimeProgress(String title, long time){
//		getProgressBarTime().setString(title);
//		getProgressBarTime().setValue((int)time);
//		parent.repaint();
//		
//	
//	}
//	
//	
//
//	
//	/**
//	 * This method initializes progressPanel	
//	 * 	
//	 * @return javax.swing.JPanel	
//	 */
//	public JPanel getComponent() {
//		if (progressPanel == null) {
//			GridBagConstraints gridBagConstraints8 = new GridBagConstraints();
//			gridBagConstraints8.gridx = 0;
//			gridBagConstraints8.weighty = 1.0;
//			gridBagConstraints8.anchor = GridBagConstraints.NORTHWEST;
//			gridBagConstraints8.gridy = 1;
//			jLabel1 = new JLabel();
//			jLabel1.setText("Time:");
//			GridBagConstraints gridBagConstraints7 = new GridBagConstraints();
//			gridBagConstraints7.gridx = 0;
//			gridBagConstraints7.weighty = 1.0;
//			gridBagConstraints7.insets = new Insets(0, 0, 5, 0);
//			gridBagConstraints7.anchor = GridBagConstraints.NORTHWEST;
//			gridBagConstraints7.gridy = 0;
//			jLabel = new JLabel();
//			jLabel.setText("Progress: ");
//			GridBagConstraints gridBagConstraints6 = new GridBagConstraints();
//			gridBagConstraints6.gridx = 1;
//			gridBagConstraints6.fill = GridBagConstraints.HORIZONTAL;
//			gridBagConstraints6.anchor = GridBagConstraints.NORTHWEST;
//			gridBagConstraints6.weighty = 1.0;
//			gridBagConstraints6.gridy = 1;
//			GridBagConstraints gridBagConstraints1 = new GridBagConstraints();
//			gridBagConstraints1.gridx = 2;
//			gridBagConstraints1.anchor = GridBagConstraints.NORTHWEST;
//			gridBagConstraints1.weightx = 0.05;
//			gridBagConstraints1.insets = new Insets(0, 10, 0, 0);
//			gridBagConstraints1.gridheight = 2;
//			gridBagConstraints1.ipady = 0;
//			gridBagConstraints1.weighty = 1.0;
//			gridBagConstraints1.gridwidth = 1;
//			gridBagConstraints1.gridy = 0;
//			GridBagConstraints gridBagConstraints = new GridBagConstraints();
//			gridBagConstraints.gridx = 1;
//			gridBagConstraints.anchor = GridBagConstraints.NORTHWEST;
//			gridBagConstraints.ipadx = 0;
//			gridBagConstraints.insets = new Insets(0, 0, 5, 0);
//			gridBagConstraints.weightx = 1.0;
//			gridBagConstraints.fill = GridBagConstraints.HORIZONTAL;
//			gridBagConstraints.weighty = 1.0;
//			gridBagConstraints.gridy = 0;
//			progressPanel = new JPanel();
//			progressPanel.setLayout(new GridBagLayout());
//			progressPanel.setSize(new Dimension(353, 63));
//			progressPanel.setBorder(BorderFactory.createTitledBorder(null, "ProgressPanel",
//				TitledBorder.DEFAULT_JUSTIFICATION, TitledBorder.DEFAULT_POSITION,
//				new Font("Dialog", Font.BOLD, 12), new Color(51, 51, 51)));
//			progressPanel.add(getProgressBar(), gridBagConstraints);
//			
//			//progressPanel.add(getProgressButton(), gridBagConstraints1);
//			progressPanel.add(getProgressBarTime(), gridBagConstraints6);
//			progressPanel.add(jLabel, gridBagConstraints7);
//			progressPanel.add(jLabel1, gridBagConstraints8);
//		}
//		return progressPanel;
//	}
//	
//	/**
//	 * This method initializes progressBar	
//	 * 	
//	 * @return javax.swing.JProgressBar	
//	 */
//	private JProgressBar getProgressBar() {
//		if (progressBar == null) {
//			progressBar = new JProgressBar(){
//		                private static final long serialVersionUID = 1L;
//
//				@Override
//				protected void paintComponent(Graphics g) {
//				    int i =0;
//				    for(InternGoal goal : goals){
//					paintGoal(g,this,i,goal.type);
//					i++;
//				    }
//				    
//			    	   
//				}  
//			};
//			
//			
//			
//		}
//		return progressBar;
//	}
//	
//	private String typeToName(SolveType type){
//	    switch(type){
//	    case SOLVABLE:
//		return "solvable";
//	    case UNKOWN:
//		return "unknown";
//	    case UNSOLVABLE:
//		return "unsolvable";
//	    	
//	    }
//	    return "";
//	}
//	
//	private String goalName(int number, SolveType type){
//	    String temp =number+". Goal";
//	    temp += number-1 == currentGoal ? ": "+getDotString() : number-1>currentGoal ? "" : ": ";
//	    return temp;
//	}
//	
//	private String goalResult(int number, SolveType type){
//            return  number-1>=currentGoal ? "" : typeToName(type);
//
//	}
//	
//	private int getStringWidth(String str){
//	    return SwingUtilities.computeStringWidth(
//		    getProgressBar().getFontMetrics(getProgressBar().getFont()),str);
//	}
//	
//	public int necessaryPanelWidth(int numberOfGoals){
//	    
//	    int w1 = getStringWidth("10. Goal: unsolvable")
//		               * numberOfGoals;
//	    int w2 = getStringWidth(jLabel.getText());
//	    return w1+w2;
//	}
//	
//	public int necessaryPanelHeight(){
//	    return getComponent().getHeight();
//	}
//	
//	private void paintGoal(Graphics g,JProgressBar bar,int number,SolveType solved){
//	
//	    Graphics gc = g.create();
//	    
//	    Graphics2D g2 = (Graphics2D)gc;
//	    g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING,
//	                         RenderingHints.VALUE_ANTIALIAS_ON);
//
//
//	   
//	   if(currentGoal <= number){
//		   gc.setColor(Color.WHITE);   
//	       }else{
//		   gc.setColor(bar.getBackground());
//	       }
//	   
//	   int max = bar.getMaximum();
//	   int fw = bar.getWidth() / max;
//	   
//	   String name = goalName(number+1,solved);
//	   String result = goalResult(number+1,solved);
//	   int widthName = SwingUtilities.computeStringWidth(g.getFontMetrics(), name);
//
//	  
//	   
//	   
//	   gc.fillRect(fw*number, 0, fw, bar.getHeight()); 
//	   
//
//
//	       
//	       gc.setColor(Color.BLACK);
//	   
//	   Shape old = gc.getClip();
//	   
//	   gc.setClip(fw*number+1, 0+1, fw-2,bar.getHeight()-2);
//	   
//	   gc.drawString(name,fw*number+2 , bar.getHeight()-4);
//	 
//	   if(solved == SolveType.UNKOWN){
//	        gc.setColor(UNKOWN_COLOR);       
//	   }else if(solved == SolveType.SOLVABLE){
//	       gc.setColor(SOLVED_COLOR);
//	   }else {
//	       gc.setColor(UNSOLVED_COLOR);
//	   }
//	   
//	   gc.drawString(result,fw*number+2+widthName , bar.getHeight()-4);
//	   
//	   gc.setClip(old);
//	      gc.setColor(Color.GRAY);
//	   gc.drawRect(fw*number, 0, fw, bar.getHeight()); 
//	  
//	   gc.dispose();
//	}
//
//
//	
//	/**
//	 * This method initializes progressBarTime	
//	 * 	
//	 * @return javax.swing.JProgressBar	
//	 */
//	private JProgressBar getProgressBarTime() {
//		if (progressBarTime == null) {
//			progressBarTime = new JProgressBar();
//		
//		}
//		return progressBarTime;
//	}
//
//
//        public void setGoalMaximum(int maximum) {
//    	    getProgressBar().setString(buildString(getProgressBar().getValue(),maximum));
//        }
//
//
//        public void setTimeMaximum(int maximum) {
//            getProgressBarTime().setMaximum(maximum);
//	    
//        }
//
//        private InternGoal findGoal(Goal goal){
//            synchronized(goals){
//            for(InternGoal g: goals){
//        	if(goal == g.goal){
//        	    return g;
//        	}
//            }
//            }
//            return null;
//        }
//
//        public void setGoalProgress(Goal goal, SolveType type) {
//            InternGoal ig = findGoal(goal);
//            if(ig != null){
//          	ig.type = type;
//        	currentGoal = ig.index+1;
//            }
//         
//           parent.repaint();
//        }
//
//
//        public void exceptionOccurred(String str,Exception e) {
//            if(!dialog.getStopRunning()){
//        	ErrorDialog.INSTANCE.showDialog("Error while executing "+ this.process.getTitle(),
//        		str, e);
//            }
//            
//            
//	    
//        }
//
//
//	/* (non-Javadoc)
//         * @see de.uka.ilkd.key.smt.SMTProgressMonitor#setFinished()
//         */
//        public void setFinished() {
//	    currentGoal = goals.size();
//	    
//        }
//
//
//
//}
