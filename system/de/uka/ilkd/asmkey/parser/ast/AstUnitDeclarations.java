// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.ast;

import de.uka.ilkd.asmkey.util.ArrayUtil;
/**
 * when parsing a unit, we encounter 3 kinds of declarations:
 * - single pass early declarations: these are parsed during the first
 *   pass and added immediately to the environment: sort, schema variables,
 *   heuristics, non derived functions and predicates.
 * - multiple pass early declarations: these are parsed also during
 *   the first pass, but necessitates many passes to gather all infos
 *   and compute all necessary infos.  derived functions and predicates, asm rules.
 * - single pass late declarations: these are parsed also in one pass, but
 *   later, as they need fully parsed functions and operatorsA
 *   taclets, lemmas.
 * the class serves as triple of array: 
 */
public class AstUnitDeclarations {
    private AstSinglePassDeclaration[] early;
    private AstMultiPassDeclaration[] multi;
    private AstSinglePassDeclaration[] late;

    public AstUnitDeclarations(AstSinglePassDeclaration[] early,
			       AstMultiPassDeclaration[] multi,
			       AstSinglePassDeclaration[] late) {
	this.early = early;
	this.multi = multi;
	this.late = late;
    }

    public AstSinglePassDeclaration[] getEarlySinglePassDeclarations() {
	return early;
    }

    public AstMultiPassDeclaration[] getMultiPassDeclarations() {
	return multi;
    }

    public AstSinglePassDeclaration[] getLateSinglePassDeclarations() {
	return late;
    }

    /** for debug only */
    public String toString() {
	return "[AstUnitDeclarations:early=" + ArrayUtil.toString(early) +
	    ";multi=" + ArrayUtil.toString(multi) +
	    ";late=" + ArrayUtil.toString(late) + "]";
    }
}
