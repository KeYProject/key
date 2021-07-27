// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.speclang.njml.JmlParser;
import org.key_project.util.collection.ImmutableList;

/**
 * A JML set statement in textual form.
 */
public final class TextualJMLSetStatement extends TextualJMLConstruct {
    
    private final JmlParser.Set_statementContext assignment;
    
    
    public TextualJMLSetStatement(ImmutableList<String> mods,
                                  JmlParser.Set_statementContext assignment) {
        super(mods);
        assert assignment != null;
        this.assignment = assignment;
        setPosition(assignment);
    }
    
    
    public JmlParser.Set_statementContext getAssignment() {
        return assignment;
    }
    
    
    @Override
    public String toString() {
        return assignment.toString();
    }
    
    
    @Override
    public boolean equals(Object o) {
        if(!(o instanceof TextualJMLSetStatement)) {
            return false;
        }
        TextualJMLSetStatement ss = (TextualJMLSetStatement) o;
        return mods.equals(ss.mods) && assignment.equals(ss.assignment);
    }
    
    
    @Override
    public int hashCode() {
        return mods.hashCode() + assignment.hashCode();
    }
}