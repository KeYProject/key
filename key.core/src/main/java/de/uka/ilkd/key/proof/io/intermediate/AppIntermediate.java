/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io.intermediate;

import de.uka.ilkd.key.logic.Name;

import org.key_project.util.collection.ImmutableList;

/**
 * Represents an intermediate rule / taclet application.
 *
 * @author Dominic Scheurer
 * @see TacletAppIntermediate
 * @see BuiltInAppIntermediate
 */
public abstract class AppIntermediate {
    private int lineNr = -1;

    /**
     * @return The new names registered in the course of this app.
     */
    public abstract ImmutableList<Name> getNewNames();

    /**
     * @return The name of this taclet / built in rule.
     */
    public abstract String getRuleName();

    /**
     * @return The line number of this application in the loaded proof file.
     */
    public String getLineNr() {
        return String.valueOf(lineNr);
    }

    /**
     * @param lineNr The line number of this application in the loaded proof file.
     */
    public void setLineNr(int lineNr) {
        this.lineNr = lineNr;
    }
}
