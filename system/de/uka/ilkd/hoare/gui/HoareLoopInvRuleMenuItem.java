package de.uka.ilkd.hoare.gui;

import java.awt.event.ActionEvent;
import java.io.StringReader;

import javax.swing.JMenuItem;
import javax.swing.JOptionPane;

import de.uka.ilkd.hoare.rule.HoareLoopInvRuleApp;
import de.uka.ilkd.hoare.rule.HoareLoopInvariantRule;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.nodeviews.BuiltInRuleMenuItem;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.parser.TermParserFactory;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.util.ExceptionHandlerException;

/**
 * rule item for the Hoare loop invariant rule as we have to throw away the context
 */
public class HoareLoopInvRuleMenuItem extends JMenuItem implements BuiltInRuleMenuItem {

    private final PosInOccurrence pio;
    private final Goal goal;
    private Term inv;
    private Term decreases;
    private final Modality modus;
    
    public HoareLoopInvRuleMenuItem(PosInOccurrence posInOccurrence, Goal goal) {
        super(HoareLoopInvariantRule.INSTANCE.displayName());
        this.pio = posInOccurrence;
        this.goal = goal;        
        this.modus = ((HoareLoopInvariantRule)connectedTo()).modus(pio);
    }
    
    protected void fireActionPerformed(ActionEvent event) {
        openDialog();
        super.fireActionPerformed(event);
    }
    
    public BuiltInRule connectedTo() {        
        return HoareLoopInvariantRule.INSTANCE;
    }
    
    /** parses the given string that represents the term (or formula)
     * using the given variable namespace and the default namespaces
     * for functions and sorts
     * @param s the String to parse
     * @param sort the expected sort
     * @param varNS the variable namespace
     */
    private Term parseTerm(String s, Namespace varNS)
        throws ParserException
    {
        NamespaceSet copy = goal.proof().getNamespaces().copy();
        copy.programVariables().add(varNS);
        Term term = TermParserFactory.createInstance().parse(
           new StringReader(s), null, goal.proof().getServices(), 
           copy, goal.proof().abbreviations());
        return term;
    }
     
    public HoareLoopInvRuleApp getRuleApp() {        
        if (inv != null) {
            if (modus == Op.DIA || modus == Op.DIATRC) {
                if (decreases != null) {
                    return new HoareLoopInvRuleApp(inv, decreases, connectedTo(), pio, goal.proof().getUserConstraint().getConstraint());
                }
            } else {                
                return new HoareLoopInvRuleApp(inv, connectedTo(), pio, goal.proof().getUserConstraint().getConstraint());
            }
        }
        return null;
    }
    
    private void openDialog() {
        inv       = getInstantiation("Enter Loop Invariant:", Sort.FORMULA);
                
        if ((modus == Op.DIA || modus == Op.DIATRC) && inv != null) {
            decreases = getInstantiation("Enter Decreasing Term:", 
                    goal.proof().getServices().getTypeConverter().
                    getIntegerLDT().targetSort());
        }
    }

    private Term getInstantiation(String message, Sort sort) {
        Term inputTerm = null;
        String inputText;
        do {
            inputText = JOptionPane.showInputDialog(message);
            if (inputText != null) {
                try {
                    inputTerm = parseTerm(inputText, goal.getVariableNamespace(new Namespace()));         
                } catch (ParserException pe) {
                    JOptionPane.showMessageDialog(Main.getInstance(), pe.getMessage());
                } catch (ExceptionHandlerException ehe) {
                    JOptionPane.showMessageDialog(Main.getInstance(), ehe.getCause() != null ? 
                            ehe.getCause().getMessage() : ehe.getMessage());
                } 
                if (inputTerm != null && !inputTerm.sort().extendsTrans(sort)) {
                    JOptionPane.showMessageDialog(Main.getInstance(),
                            "The entered " + (sort == Sort.FORMULA ? "invariant must be a formula, but is of type " + sort : 
                                "decreases term must have sort int."));
                    inputTerm = null;
                }
            } else {
                inputTerm = null;
            }
        } while (inputTerm == null && inputText != null);
        return inputTerm;
    }
    
}
