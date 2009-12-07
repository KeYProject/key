// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest;

import java.util.Set;

public abstract class DecProdModelGenerator{

    /** Stop model generation as soon as possible even if no model was created. (Otherwise this thread will be stopped)*/
    public volatile boolean  terminateAsSoonAsPossible=false;

    public Set<Model> createModels(){return null;};

}
