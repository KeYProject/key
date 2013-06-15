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


package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.sort.Sort;

/** 
 * In contrast to the distinction of formulas and terms as made by most of the 
 * inductive definitions of the syntax of a logic, an instance of this class can
 * stand for a term or a formula. This is done for implementation reasons, as
 * their structure is quite similar and there are good reasons concerning the
 * software's design/architecture (for example using same visitors, reduction of
 * case distinction, unified interfaces etc.). However, they are strictly
 * separated by their sorts. A formula (and just a formula) must have 
 * the sort {@link Sort#FORMULA}. Terms of a different sort are terms in the
 * customary logic sense. A term of sort formula is allowed exact there, where a
 * formuala in logic is allowed to appear, same for terms of different sorts. 
 *   Some words about other design decisions: 
 * <ol> 
 *  <li> terms are immutable, this means after a term object is created, it
 *  cannot be changed. The advantage is that we can use term sharing and
 *  saving a lot of memory space. 
 *  </li>
 *  <li> Term has to be created using the {@link TermFactory} and
 *    <emph>not</emph> by using the constructors itself. 
 *  </li>
 *  <li> Term is subclassed, but all subclasses have to be package private, so
 *    that all other classes except {@link TermFactory} know only the class
 *    Term and its interface. Even most classes of the logic package.
 *  </li>
 *  <li> as it is immutable, most (all) attributes should be declared final
 * </li>
 * </ol>
 * Term supports the {@link Visitor} pattern. Two different visit strategies are
 * currently supported: {@link Term#execPostOrder(Visitor)} and
 * {@link Term#execPreOrder(Visitor)}. 
 */
public interface Term extends SVSubstitute, Sorted {
    
    /** 
     * The top operator (e.g., in "A and B" this is "and", in f(x,y) it is "f").
     */
    public Operator op();
    
    /**
     * The subterms.
     */
    public ImmutableArray<Term> subs();
        
    /** 
     * The <code>n</code>-th direct subterm.
     */
    public Term sub(int n);
        
    /**
     * The (possibly indirect) subterm specified by a PosInTerm.
     */
    public Term subAt(PosInTerm pos);
        
     /**
     * The logical variables bound by the top level operator.
     */
    public ImmutableArray<QuantifiableVariable> boundVars();

    /**
     * The logical variables bound by the top level operator for the nth 
     * subterm.
     */
    public ImmutableArray<QuantifiableVariable> varsBoundHere(int n);
    
    /**
     * The Java block at top level.
     */
    public JavaBlock javaBlock();
    
    /**
     * The arity of the term.   
     * */
    public int arity();
    
    /**
     * The sort of the term.
     */
    public Sort sort();    
    
    /**
     * The nesting depth of this term.
     */
    public int depth();
    
    /**
     * Whether all operators in this term are rigid.
     */
    public boolean isRigid();
    
    /** 
     * The set of free quantifiable variables occurring in this term.
     */
    public ImmutableSet<QuantifiableVariable> freeVars();
    
    /** 
     * The visitor is handed through till the bottom of the tree and
     * then it walks upwards, while at each upstep the method visit of
     * the visitor is called.
     * @param visitor the Visitor
     */
    public void execPostOrder(Visitor visitor);

    /** 
     * The visitor walks downwards the tree, while at each downstep the method 
     * visit of the visitor is called.
     * @param visitor the Visitor
     */
    public void execPreOrder(Visitor visitor);
    
    /**
     * Compares if two terms are equal modulo bound renaming
     * @return true iff the given Term has the same values in
     * operator, sort, arity, varsBoundHere and javaBlock as this object
     * modulo bound renaming
     */  
    public boolean equalsModRenaming(Object o);  
    
    /**
     * returns true if the term is labeled
     */
    public boolean hasLabels();
    
    /**
     * checks if the given label is attached to the term
     * @param label the ITermLabel for which to look (must not be null)
     */
    public boolean containsLabel(ITermLabel label);
    
    /**
     * returns list of labels attached to this term
     * @return list of labels (maybe be empty but never <code>null</code>
     */
    public ImmutableArray<ITermLabel> getLabels();
    
    /**
     * Returns a serial number for a term. The serial number is not persistent.
     */
    public int serialNumber();
    
    
    /**
     * Checks if the {@link Term} or one of its direct or indirect children
     * contains a non empty {@link JavaBlock}. 
     * @return {@code true} The {@link Term} or one of its direct or indirect children contains a non empty {@link JavaBlock}, {@code false} no {@link JavaBlock} available.
     */
    public boolean isContainsJavaBlockRecursive();
}
