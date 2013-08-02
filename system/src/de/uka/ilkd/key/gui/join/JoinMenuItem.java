// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.join;

import java.awt.event.ActionEvent;
import java.util.List;

import javax.swing.AbstractAction;
import javax.swing.JMenuItem;
import javax.swing.SwingUtilities;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.notification.events.ExceptionFailureEvent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.join.JoinProcessor;
import de.uka.ilkd.key.proof.join.JoinProcessor.Listener;
import de.uka.ilkd.key.proof.join.PredicateEstimator;
import de.uka.ilkd.key.proof.join.ProspectivePartner;
import de.uka.ilkd.key.util.ExperimentalFeature;


public class JoinMenuItem extends JMenuItem {

    private static final long serialVersionUID = -2602116358650063634L;

    /** Controls whether joining is available to the user.
     * WARNING: You may refresh your GUI elements after (de-)activation.
     */
    public static final ExperimentalFeature FEATURE = new ExperimentalFeature(){
        private boolean active = true;
        @Override
        public void deactivate() { active = false; }

        @Override
        public void activate() {
            de.uka.ilkd.key.proof.delayedcut.DelayedCut.FEATURE.activate();
            active = true;
        }

        @Override
        public boolean active() { return active; }
    };


    public JoinMenuItem(final List<ProspectivePartner> partner, final Proof proof, final KeYMediator mediator) {
    super();

        this.setText(toString());
        this.setAction(new AbstractAction(toString()) {

            private static final long serialVersionUID = 1L;

            @Override
            public void actionPerformed(ActionEvent e) {
                 mediator.stopInterface(true);
                 JoinDialog dialog = new JoinDialog(partner,
                		 		proof,PredicateEstimator.STD_ESTIMATOR,proof.getServices());
                 dialog.setVisible(true);
                 if(dialog.okayButtonHasBeenPressed()){
                	 start(dialog.getSelectedPartner(),proof,mediator);
                 }else{
                	 mediator.startInterface(true);
                 }

            }
        });
    }

    private void start(ProspectivePartner partner, Proof proof, final KeYMediator mediator){


        JoinProcessor processor = new JoinProcessor(partner, proof);

        processor.addListener(new Listener() {

           @Override
           public void exceptionWhileJoining(Throwable e) {
              mediator.notify(new ExceptionFailureEvent(e.getMessage(), e));
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

        Thread thread = new Thread(processor,"ProofJoinProcessor");
        thread.start();
    }


    @Override
    public String toString() {
        return "Join goal with...";
    }
}