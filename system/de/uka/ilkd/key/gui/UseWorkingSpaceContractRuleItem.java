package de.uka.ilkd.key.gui;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import javax.swing.JFrame;
import javax.swing.JMenuItem;

import de.uka.ilkd.key.jml.JMLMethodSpec;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.WorkingSpaceRigidOp;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.UseWorkingSpaceContractRule;
import de.uka.ilkd.key.rule.WorkingSpaceContractRuleApp;

public class UseWorkingSpaceContractRuleItem extends JMenuItem implements
        BuiltInRuleMenuItem {

    private UseWorkingSpaceContractRule connectedTo;
    private Proof proof;
    private PosInOccurrence pos;
    private WorkingSpaceContractRuleApp app;
    private JFrame parent;    

    /** the added action listeners */
    private List listenerList = new LinkedList();

    
    public UseWorkingSpaceContractRuleItem(JFrame parent, UseWorkingSpaceContractRule rule, 
                                     Proof proof, PosInOccurrence pos) {
        super(rule.name().toString());
        this.connectedTo = rule;
        this.pos = pos;
        this.parent = parent;
        this.proof = proof;
        
        super.addActionListener(new ActionListener() {

            public void actionPerformed(ActionEvent e) { 
                    openDialog(e);
            }
            
        });                  

    }
    
    public void openDialog(ActionEvent e) {

        WorkingSpaceContractDialog dialog
        = new WorkingSpaceContractDialog("Working Space Contract chooser", 
                parent, proof.getServices());
        JMLMethodSpec spec = connectedTo.selectSpec(proof, pos, dialog);
        int compare = dialog.compare();
        if (spec!=null) {
            app = new WorkingSpaceContractRuleApp(connectedTo, pos, 
                    Constraint.BOTTOM, spec, compare);
            processUseWorkingSpaceContractRuleSelected(e);
        }
    }
    
    public BuiltInRule connectedTo() {
        return connectedTo;
    }
    
    public WorkingSpaceContractRuleApp getRuleApp() {
        return app;
    }
    
    protected void processUseWorkingSpaceContractRuleSelected(ActionEvent e) {
        final Iterator it = listenerList.iterator();
        while (it.hasNext()) {
            ((ActionListener)it.next()).actionPerformed(e);
        }
    }
    
    public void addActionListener(ActionListener listener) {
        listenerList.add(listener);
    }

    public void removeActionListener(ActionListener listener) {
        listenerList.remove(listener);
    }

}
