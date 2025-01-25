/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;


import org.jspecify.annotations.Nullable;

/**
 * class contains optional attributes of a Taclet.
 */
public final class TacletAttributes {

    private @Nullable String displayName;
    private @Nullable String helpText;

    /** trigger related information */
    private @Nullable Trigger trigger;



    public TacletAttributes() {
        this.displayName = null;
        this.helpText = null;
    }


    public @Nullable String displayName() {
        return displayName;
    }

    public @Nullable String helpText() {
        return helpText;
    }

    /**
     * sets an optional display name (presented to the user)
     */
    public void setDisplayName(@Nullable String s) {
        displayName = s;
    }

    public void setHelpText(@Nullable String s) {
        helpText = s;
    }


    public Trigger getTrigger() {
        return trigger;
    }


    public void setTrigger(Trigger trigger) {
        this.trigger = trigger;
    }


}
