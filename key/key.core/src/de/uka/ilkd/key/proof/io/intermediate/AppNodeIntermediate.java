/**
 * 
 */
package de.uka.ilkd.key.proof.io.intermediate;

/**
 * Node in an intermediate proof representation storing a rule application.
 * 
 * @author Dominic Scheurer
 */
public class AppNodeIntermediate extends NodeIntermediate {

    private AppIntermediate ruleApp = null;
    private boolean interactiveRuleApplication = false;

    public AppIntermediate getIntermediateRuleApp() {
        return ruleApp;
    }
    
    public void setIntermediateRuleApp(AppIntermediate ruleApp) {
        this.ruleApp = ruleApp;
    }

    public boolean isInteractiveRuleApplication() {
        return interactiveRuleApplication;
    }

    public void setInteractiveRuleApplication(boolean interactiveRuleApplication) {
        this.interactiveRuleApplication = interactiveRuleApplication;
    }
    
}