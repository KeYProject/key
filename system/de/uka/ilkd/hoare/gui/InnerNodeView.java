package de.uka.ilkd.hoare.gui;

import java.io.IOException;

import de.uka.ilkd.hoare.pp.HoareLogicPrettyPrinter;
import de.uka.ilkd.hoare.rule.HoareLoopInvRuleApp;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.configuration.ConfigChangeEvent;
import de.uka.ilkd.key.gui.configuration.ConfigChangeListener;
import de.uka.ilkd.key.gui.nodeviews.NonGoalInfoView;
import de.uka.ilkd.key.pp.ConstraintSequentPrintFilter;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

public class InnerNodeView extends NonGoalInfoView {

    public InnerNodeView(Node node, KeYMediator mediator) {
        super(node, mediator);        
    }
    
    protected void printInnerNode(Node node, KeYMediator mediator) {
        filter = new ConstraintSequentPrintFilter 
        ( node.sequent (), mediator.getUserConstraint ().getConstraint () );  
        printer = new HoareLogicPrettyPrinter
        (new ProgramPrinter(null),
                mediator.getNotationInfo(),
                mediator.getServices());

        printer.printSequent (null, filter);
        String s = printer.toString();
        RuleApp app = node.getAppliedRuleApp();
        s += "\nNode Nr "+node.serialNr()+"\n";

        if ( app != null ) {
            s = s + "\n \nUpcoming rule application: " + 
                app.rule().displayName();
            if (!app.rule().displayName().equals(app.rule().name().toString())) {
                s += " (" + app.rule().name() + ")";
            }
            s += "\n";
            LogicPrinter tacPrinter = new HoareLogicPrettyPrinter
            (new ProgramPrinter(null),
                    mediator.getNotationInfo(),
                    mediator.getServices(), true);
            
            if (app.rule() instanceof Taclet) {               
                ((HoareLogicPrettyPrinter)tacPrinter).printTaclet((TacletApp)app);
                s += tacPrinter;
            } else if (app instanceof HoareLoopInvRuleApp) {
                try {
                    ((HoareLogicPrettyPrinter)tacPrinter).
                        printWhileRule((HoareLoopInvRuleApp) app);
                } catch (IOException e) {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                }
                s += tacPrinter;
            } else {
                s = s + app.rule();
            }
        }
        
        Config.DEFAULT.addConfigChangeListener(
            new ConfigChangeListener() {
                    public void configChanged(ConfigChangeEvent e) {
                        updateUI();
                    }
                });

        updateUI();
        setText(s);

        if (app!=null) {         
            highlightRuleAppPosition(app);       
        } else {         
            // no rule app       
                 setCaretPosition(0);    
        }
        
        setEditable(false);
    }

}
