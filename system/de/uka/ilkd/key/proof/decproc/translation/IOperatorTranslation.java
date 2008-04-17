// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc.translation;

import de.uka.ilkd.key.logic.op.Operator;

/** This interface represents a rule for translating KeY <tt>Term</tt>s into SMT-LIB 
 * <tt>Term</tt>s and <tt>Formula</tt>e.
 * <p>
 * A rule offers two methods: One for checking if this rule is applicable on a given
 * <tt>Operator</tt> of a <tt>Term</tt> and one that actually performs the translation
 *  
 * @author akuwertz
 * @version <pre>
 * 1.0,
 * 1.1,  01/28/2006  (Added comments)</pre>
 */
public interface IOperatorTranslation {
    
    
    /** Returns <tt>true</tt> if this translation rule can be applied to the given 
     * <tt>Operator</tt>
     * 
     * @param op the <tt>Operator</tt> to be checked for applicability
     * @return true iff the specified <tt>Operator</tt> can be translated by this rule
     */
    public boolean isApplicable(Operator op);
    
    
    /** Returns an SMT-LIB <tt>Term</tt> or <tt>Formula</tt> as translation result of the
     * specified <tt>Operator</tt>
     * 
     * @param op the <tt>Operator</tt> to be translated
     * @param ttVisitor the <tt>TermTranslationVisitor</tt> on which the translation is performed 
     * @return an SMT-LIB <tt>Term</tt> or <tt>Formula</tt> representing the translation of
     *         the specified <tt>Operator</tt>
     *         
     * @throws IllegalArgumentException if one of the arguments of the specified <tt>Operator</tt>
     *                                  on the stack of <tt>ttVisitor</tt> has an illegal type
     * @throws UnsupportedOperationException if the specified <tt>Operator</tt> can not be 
     *                                       translated          
     */
    public Object translate(Operator op, TermTranslationVisitor ttVisitor);
    
}
