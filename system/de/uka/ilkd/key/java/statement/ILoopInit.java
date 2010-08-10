// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.LoopInitializer;
import de.uka.ilkd.key.java.TerminalProgramElement;

public interface ILoopInit extends TerminalProgramElement {

    int size();

    ImmutableArray<LoopInitializer> getInits();

}
