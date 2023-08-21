/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;


/**
 * class contains optional attributes of a Taclet.
 */
public final class TacletAttributes {

    private String displayName;
    private String helpText;

    /** trigger related information */
    private Trigger trigger;



    public TacletAttributes() {
        this.displayName = null;
        this.helpText = null;
    }


    public String displayName() {
        return displayName;
    }

    public String helpText() {
        return helpText;
    }

    /**
     * sets an optional display name (presented to the user)
     */
    public void setDisplayName(String s) {
        displayName = s;
    }

    public void setHelpText(String s) {
        helpText = s;
    }


    public Trigger getTrigger() {
        return trigger;
    }


    public void setTrigger(Trigger trigger) {
        this.trigger = trigger;
    }


}
