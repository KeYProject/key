// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.encapsulation;


interface TypeScheme {
    public TypeScheme combineWith(TypeScheme ts);
    
    public boolean subSchemeOf(TypeScheme ts);
    
    public boolean equalTo(TypeScheme ts);
}
