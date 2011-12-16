package de.uka.ilkd.key.gui.join;

import java.awt.event.ActionEvent;
import java.util.List;

import javax.swing.AbstractAction;
import javax.swing.JMenuItem;
import javax.swing.SwingUtilities;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.utilities.InspectorForFormulas;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.join.JoinProcessor;
import de.uka.ilkd.key.proof.join.JoinProcessor.Listener;
import de.uka.ilkd.key.proof.join.PredicateEstimator;
import de.uka.ilkd.key.proof.join.ProspectivePartner;


public class JoinMenuItem extends JMenuItem {
    private static final long serialVersionUID = 1L;
  

    public JoinMenuItem(final List<ProspectivePartner> partner, final Proof proof, final KeYMediator mediator) {
    super();    

        this.setText(toString());
        this.setAction(new AbstractAction(toString()) {
            
            private static final long serialVersionUID = 1L;

            @Override
            public void actionPerformed(ActionEvent e) {
                 mediator.stopInterface(true);
                 JoinDialog dialog = new JoinDialog(new InspectorForFormulas(proof.getServices()),
                         partner, proof,PredicateEstimator.STD_ESTIMATOR);
                 dialog.setVisible(true);
                 if(dialog.okayButtonHasBeenPressed()){
                      
                        
                     JoinProcessor processor = new JoinProcessor(dialog.getSelectedPartner(), proof);
                     
                     processor.addListener(new Listener() {
                        
                        @Override
                        public void exceptionWhileJoining(Throwable e) {
                           ExceptionDialog.showDialog(mediator.mainFrame(), e);   
                           mediator.startInterface(true);
                        }
                        
                        @Override
                        public void endOfJoining(final ImmutableList<Goal> goals) {
                            SwingUtilities.invokeLater(new Runnable() {
                                
                                @Override
                                public void run() {
                                    mediator.startInterface(true);
                                    mediator.startAutoMode(goals);
                                   
                                    
                                }
                            });
           
                       
                        }
                    });
                     
                     Thread thread = new Thread(processor);
                     thread.start();
                   
                 }
                 
            }
        });
    }
    
 
    @Override
    public String toString() {
        return "Join goal with...";
    }
}