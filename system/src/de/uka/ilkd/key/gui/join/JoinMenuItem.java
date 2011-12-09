package de.uka.ilkd.key.gui.join;

import java.awt.event.ActionEvent;
import java.util.List;

import javax.swing.AbstractAction;
import javax.swing.JMenuItem;

import de.uka.ilkd.key.gui.utilities.InspectorForFormulas;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.join.PredicateEstimator;
import de.uka.ilkd.key.proof.join.ProspectivePartner;


public class JoinMenuItem extends JMenuItem {
    private static final long serialVersionUID = 1L;
  

    public JoinMenuItem(final List<ProspectivePartner> partner, final Proof proof) {
    super();    

        this.setText(toString());
        this.setAction(new AbstractAction(toString()) {
            
            private static final long serialVersionUID = 1L;

            @Override
            public void actionPerformed(ActionEvent e) {
                 JoinDialog dialog = new JoinDialog(new InspectorForFormulas(proof.getServices()),
                         partner, proof,PredicateEstimator.STD_ESTIMATOR);
                 dialog.setVisible(true);
                 
            }
        });
    }
    
 
    @Override
    public String toString() {
        return "Join goal with...";
    }
}