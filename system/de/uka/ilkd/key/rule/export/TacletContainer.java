// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
/*
 * Created on 07.12.2004
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package de.uka.ilkd.key.rule.export;

import de.uka.ilkd.key.logic.Named;

/**
 * @author stenger
 *
 * This interface generalizes the concept of a named set of taclets,
 * like a rule set, a .key file, etc.
 */
public interface TacletContainer extends Named {
    ListOfTacletModelInfo getTaclets ();
}
