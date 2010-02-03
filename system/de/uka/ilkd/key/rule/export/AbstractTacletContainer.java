// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//This file is part of KeY - Integrated Deductive Software Design 
//Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                      and Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License.
//See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.export;

import de.uka.ilkd.key.logic.Name;



public abstract class AbstractTacletContainer implements TacletContainer {
    private ListOfTacletModelInfo taclets = SLListOfTacletModelInfo.EMPTY_LIST;

    public ListOfTacletModelInfo getTaclets () {
        return taclets;
    }
    
    public void setTaclets ( ListOfTacletModelInfo p_taclets ) {
        taclets = p_taclets;
    }
    
    public void addTaclet ( TacletModelInfo p_taclet ) {
        taclets = taclets.prepend ( p_taclet );
    }

    public abstract Name name ();

}
