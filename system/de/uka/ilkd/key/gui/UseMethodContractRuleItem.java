package de.uka.ilkd.key.gui;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import javax.swing.JFrame;
import javax.swing.JMenuItem;

import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.OldOperationContract;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.ContractConfigurator;
import de.uka.ilkd.key.rule.MethodContractRuleApp;
import de.uka.ilkd.key.rule.UseMethodContractRule;

public class UseMethodContractRuleItem extends JMenuItem implements BuiltInRuleMenuItem{
    
    private UseMethodContractRule connectedTo;
    private Proof proof;
    private PosInOccurrence pos;
    private MethodContractRuleApp app;
    private JFrame parent;    

    /** the added action listeners */
    private List listenerList = new LinkedList();

    
    public UseMethodContractRuleItem(JFrame parent, UseMethodContractRule rule, 
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
        ContractConfigurator config 
            = new DefaultContractConfigurator("Contract Configurator", parent);
        OldOperationContract mc = connectedTo.selectContract(proof, pos, config);
        if (mc!=null) {
            app = new MethodContractRuleApp(connectedTo, pos, Constraint.BOTTOM, mc);
            processUseMethodContractRuleSelected(e);
        }
    }
    
    public BuiltInRule connectedTo() {
        return connectedTo;
    }
    
    public MethodContractRuleApp getRuleApp() {
        return app;
    }
    
    protected void processUseMethodContractRuleSelected(ActionEvent e) {
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
