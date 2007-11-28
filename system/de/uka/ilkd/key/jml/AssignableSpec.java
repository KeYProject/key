// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.jml;

import de.uka.ilkd.key.logic.SetOfLocationDescriptor;

public interface AssignableSpec{

    void addAssignable(SetOfLocationDescriptor locations);

    SetOfLocationDescriptor getAssignable();

    void setAssignableMode(String s);

    String getAssignableMode();

}
