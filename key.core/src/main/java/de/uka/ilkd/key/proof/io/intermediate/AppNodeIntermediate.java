/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io.intermediate;

/**
 * Node in an intermediate proof representation storing a rule application.
 *
 * @author Dominic Scheurer
 */
public class AppNodeIntermediate extends NodeIntermediate {

    private AppIntermediate ruleApp = null;
    private boolean interactiveRuleApplication = false;
    /** Signals that this app has been triggered by a proof script. */
    private boolean scriptRuleApplication = false;
    /** user-provided notes for the node */
    private String notes = null;

    public AppIntermediate getIntermediateRuleApp() {
        return ruleApp;
    }

    public void setIntermediateRuleApp(AppIntermediate ruleApp) {
        this.ruleApp = ruleApp;
    }

    public boolean isInteractiveRuleApplication() {
        return interactiveRuleApplication;
    }

    public boolean isScriptRuleApplication() {
        return scriptRuleApplication;
    }

    public void setInteractiveRuleApplication(boolean interactiveRuleApplication) {
        this.interactiveRuleApplication = interactiveRuleApplication;
    }

    public void setScriptRuleApplication(boolean scriptRuleApplication) {
        this.scriptRuleApplication = scriptRuleApplication;
    }

    public void setNotes(String notes) {
        this.notes = notes;
    }

    public String getNotes() {
        return notes;
    }
}
