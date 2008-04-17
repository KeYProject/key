// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;


/**
 * This implements an <tt>ifEx (x1, x2, ...) (phi) (t1) (t2)</tt> operator.
 * The meaning of this expression is given by
 * <tt> (ifEx (x1, x2, ...) (phi) (t1) (t2)) equiv (ifEx (x1) (ex x2. ... phi) (ifEx (x2, ...) (phi) (t1) (t2)) (t2))</tt>
 * and by
 * <tt>(ifEx (x1) (phi) (t1) (t2)) equiv (if (ex x1. phi) ({x1 (min x1. phi)}t1) (t2))</tt>
 */
public class IfExThenElse extends IfThenElse {
    
    IfExThenElse () {
        super ( new Name ( "ifEx-then-else" ) );
    }
    
}
