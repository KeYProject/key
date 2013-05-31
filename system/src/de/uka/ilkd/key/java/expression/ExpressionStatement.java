// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



package de.uka.ilkd.key.java.expression;


import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.LoopInitializer;

/** 
 *  An ExpressionStatement is a statement that may appear as an expression.
 *  There are three subclasses: MethodReference, Assignment, and New.
 *  Strictly speaking, Java would allow any expression as a statement;
 *  however, this does not make much sense (except backward compatibility to
 *  awkward C code) and is even forbidden in dialects (such as Generic Java).
 */

public interface ExpressionStatement extends Expression, LoopInitializer {
}
