package de.uka.ilkd.key.gui.join;

import java.awt.event.ActionEvent;
import java.util.List;

import javax.swing.AbstractAction;
import javax.swing.JMenuItem;

import de.uka.ilkd.key.proof.join.ProspectivePartner;


public class JoinMenuItem extends JMenuItem {
    private static final long serialVersionUID = 1L;
    private final List<ProspectivePartner> partner;

    public JoinMenuItem(final List<ProspectivePartner> partner) {
    super();    
        this.partner = partner;
        this.setText(toString());
        this.setAction(new AbstractAction(toString()) {
            
            private static final long serialVersionUID = 1L;

            @Override
            public void actionPerformed(ActionEvent e) {
                 ProspectivePartner p = partner.get(0);
                 System.out.println(p.getCommonParent().serialNr());

                 System.out.println(p.getCommonPredicate());
            }
        });
    }
    
    public  List<ProspectivePartner>  getPartner() {
            return partner;
    }
    
    @Override
    public String toString() {
        return "Join goal with...";
    }
}