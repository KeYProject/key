// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.rule.export;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.Name;



public abstract class AbstractTacletContainer implements TacletContainer {
    private ImmutableList<TacletModelInfo> taclets = ImmutableSLList.<TacletModelInfo>nil();

    public ImmutableList<TacletModelInfo> getTaclets () {
        return taclets;
    }
    
    public void setTaclets ( ImmutableList<TacletModelInfo> p_taclets ) {
        taclets = p_taclets;
    }
    
    public void addTaclet ( TacletModelInfo p_taclet ) {
        taclets = taclets.prepend ( p_taclet );
    }

    public abstract Name name ();

}
