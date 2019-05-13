// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.io.intermediate;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Name;

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
        return "" + lineNr;
    }

    /**
     * @param lineNr The line number of this application in the loaded proof file.
     */
    public void setLineNr(int lineNr) {
        this.lineNr = lineNr;
    }
}
