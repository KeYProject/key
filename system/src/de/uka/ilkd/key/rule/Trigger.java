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

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;

public class Trigger {

    /** trigger related information */
    private final Term trigger;
    private final ImmutableList<Term> avoidConditions;
    private final SchemaVariable triggerVar;
    
    
    public Trigger(SchemaVariable triggerVar, Term trigger,  
            ImmutableList<Term> avoidConditions) {
        assert triggerVar != null;
        assert trigger != null;
        assert avoidConditions != null;
        
        this.triggerVar = triggerVar;
        this.trigger = trigger;
        this.avoidConditions = avoidConditions;
    }


    public SchemaVariable getTriggerVar() {
        return triggerVar;
    }

    public Term getTerm() {
        return trigger;
    }

    public ImmutableList<Term> getAvoidConditions() {
        return avoidConditions;
    }

    public boolean hasAvoidConditions() {
        return !avoidConditions.isEmpty();
    }
    
}