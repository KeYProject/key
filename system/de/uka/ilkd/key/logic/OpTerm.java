// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.Metavariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;

/** 
 * The OpTerm class is used to represent a term whose top level operator does not bind 
 * variables and that has no program. For example terms with a function symbol on top or
 * formulas with a predicates symbol but also more complex ones with the usual propositional
 * connectives. It is for example not used in cases where the top level operator represents
 * a quantifier, modality, an update or an ifex-then-else operator.  
 *   Instances <strong>must never</strong> be accessed via this interface, use the interface
 * of the superclass Term and construct instances only via a TermFactory instead. The 
 * OpTerm class contains four different implementations for nullary, unary, binary and 
 * arbitrary (but fixed) arity. The ratinale behind this is to avoid unneccessary allocation
 * of array for the most common cases.
 */
abstract class OpTerm extends Term {


    /**
     * creates an OpTerm and selects the most sepcific implementation
     * of OpTerm.
     * @param op the Operator on the top 
     * @param subs an array of Term containing the sub terms or formulas. The array may 
     * not be null neither one its components. To create a nullary term the given array 
     * must have length zero.
     * @return the created term <tt>op(subs[0],...,subs[subs.length-1])</tt>
     */
    public static Term createOpTerm(Operator op, Term[] subs) {        
        if (subs.length == 0) {
            return new ConstantOpTerm(op);
        } else if (subs.length == 1) {
            return new UnaryOpTerm(op, subs);
        } else if (subs.length == 2) {
            return new BinaryOpTerm(op, subs);
        } 
        
        return new ArbitraryOpTerm(op, subs);
    }
    
    /**
     * creates a binary term <tt>op(left, right)</tt>
     * @param op the operator on the top
     * @param left a Term used as first subterm (must not be null)
     * @param right a Term used as second subterm (must not be null)
     * @return the created term <tt>op(left, right)</tt>
     */
    public static Term createBinaryOpTerm(Operator op, Term left, Term right) {
        return new BinaryOpTerm(op, new Term[]{left, right});
    }
    
    /**
     * creates a unary term <tt>op(sub)></tt>
     * @param op the operator on the top
     * @param sub the Term  to be used as subterm (must not be null)
     * @return the created term <tt>op(sub)</tt>
     */
    public static Term createUnaryOpTerm(Operator op, Term sub) {
        return new UnaryOpTerm(op, new Term[]{sub});
    }

    /**
     * creates a nullary/constant term <tt>op</tt>
     * @param op the operator on the top
     * @return the created term <tt>op</tt>
     */
    public static Term createConstantOpTerm(Operator op) {
        return new ConstantOpTerm(op);
    }
    
    /** 
     * initialises the term with the given operator and sort.
     * It updates the set of free variables and meta variables by 
     * adding the operator if necessary. 
     * <em>Attention:</em> The constructor of the subclasses have to invoke 
     * {@link #fillCaches()} at the end.
     * @param op the Operator on top
     * @param sort the Sort of the term
     */
    protected OpTerm(Operator op, Sort sort) {
        super(op, sort);       
        
        if (op instanceof QuantifiableVariable) {
            freeVars = freeVars.add((QuantifiableVariable) op);
        } else if ( op instanceof Metavariable ) {
            metaVars = metaVars.add ( (Metavariable)op );
        }
    }
    
    /**
     * an instance of an {@link OpTerm} binds no variables on its top level
     * therefore we return the empty list here.
     */
    public ArrayOfQuantifiableVariable varsBoundHere(int n) {
        return EMPTY_VAR_LIST;
    }

    /**
     * represents an term of an arbitrary arity. While this implementation works
     * for any arity. There exist special faster and memory resource saving
     * implementation for arities lesser or equal than two.
     */
    static class ArbitraryOpTerm extends OpTerm {

        /** the arry containing the sub terms */
        private final ArrayOfTerm subTerm;

        /** the depth of the term */
        private int depth = -1;
        
        /** creates an OpTerm with top operator op, some subterms and a sort
         * @param op Operator at the top of the termstructure that starts
         * here
         * @param subTerm an array containing subTerms (an array with length 0 if
         * there are no more subterms
         */
        ArbitraryOpTerm(Operator op, Term[] subTerm) {
            super(op, op.sort(subTerm));
            
            this.subTerm   = new ArrayOfTerm(subTerm);
                        
            fillCaches();	
        }   

        /**
         * computes the maximal depth of the term and caches its value. Afterwards
         * the fillCaches of the superclass is invoked. 
         */
        protected void fillCaches() {
            int max_depth = -1;
            for (int i = 0, sz = arity(); i < sz; i++) {
                final int subTermDepth = sub(i).depth();
                if (subTermDepth > max_depth) {
                    max_depth = subTermDepth;   
                }
            }

            depth = max_depth + 1;

            super.fillCaches();
        }
          
        /** @return arity of the term */
        public int arity() {
            return subTerm.size();
        }

        /** the nr-th subterm */
        public Term sub(int nr) {
            return subTerm.getTerm(nr);        
        }

        /** @return an empty variable list */
        public ArrayOfQuantifiableVariable varsBoundHere(int n) {
            return EMPTY_VAR_LIST;
        }

        /** @return the maximal depth of the term */
        public int depth() {
            return depth;
        }
    }
     
    /**
     * this implementation represents an OpTerm with exactly two 
     * sub terms
     */
    static class BinaryOpTerm extends OpTerm {

        /** the first subterm */
        private final Term left;
        /** the second subterm */
        private final Term right;

        /** the terms maximal depth */
        private int depth = -1;
        
        /**
         * creates a binary term
         * @param op the Operator on the top
         * @param subs the array of Term containing the subterms to be used
         * <strong>must have</strong> length two and be non-null for all its components.
         */
        BinaryOpTerm(Operator op, Term[] subs) {
            super(op,op.sort(subs));
            assert subs.length == 2 : "Tried to create a binary term with more or less" +
            " than two sub terms";
            assert subs[0] != null && subs[1] != null : "Tried to create a term with 'null' as subterm.";
            this.left  = subs[0];
            this.right = subs[1];        
            
            fillCaches();
        }
           
        /** 
         * returns the arity of the term which is in this case <tt>2</tt>
         */
        public int arity() {
            return 2;
        }

        /**
         * returns the depth of the term 
         */
        public int depth() {
            if (depth == -1) {
                final int leftDepth = left.depth();
                final int rightDepth = right.depth();
                depth = (leftDepth > rightDepth ? leftDepth : rightDepth) + 1; 
            }
            return depth;
        }

        /**
         * returns the <tt>nr</tt> sub terms
         */
        public Term sub(int nr) {
            if (nr < 0 || nr >= arity()) {
                throw new IndexOutOfBoundsException("Term " + this + " has arity " + arity());
            }
            return nr == 0 ? left : right;
        }
    }

    /**
     * this implementation is tailored towards unary terms 
     */
    static class UnaryOpTerm extends OpTerm {

        /** the subterm */
        private final Term sub;

        /** the Term's depth */
        private int depth = -1;
        
        /** creates a unary term         
         * @param op the Operator on top
         * @param sub the Term used as the one subterm (<em>must not</em> be null)
         */
        UnaryOpTerm(Operator op, Term sub) {
            this(op, new Term[]{sub});            
        }
        
        /** creates a unary term         
         * @param op the Operator on top
         * @param subs the array of Term of length one with the one subterm (<em>must not</em> be null)
         */
        UnaryOpTerm(Operator op, Term[] subs) {
            super(op,op.sort(subs));
            assert subs.length == 1 : "Tried to create a unary term with more or less" +
                        " than one sub term";
            assert subs[0] != null : "Tried to create a term with 'null' as subterm.";
            this.sub  = subs[0];
            fillCaches();
        }
           
        /**
         * returns the arity of the term which is for a unary one simply <tt>1</tt>
         */
        public int arity() {
            return 1;
        }

        /**
         * retrieves the terms depth
         * @return the depth of the term
         */
        public int depth() {
            if (depth == -1) {
                depth = sub.depth() + 1; 
            }
            return depth;
        }

        /** 
         * returns the <nr>-th subterm
         */
        public Term sub(int nr) {
            if (nr != 0) {
                throw new IndexOutOfBoundsException("Term " + this + " has arity " + arity());
            }
            return sub;
        }       
    }

    /**
     * Represents a nullary OpTerm.
     */
    static class ConstantOpTerm extends OpTerm {

        private final static Term[] NOSUBS = new Term[0];
        
        /**
         * creates the nullary op term
         * @param op the Operator on the top
         */
        ConstantOpTerm(Operator op) {
            super(op,op.sort(NOSUBS));
            fillCaches();
        }
           
        public int arity() {
            return 0;
        }
        
        public int depth() {
            return 0;
        }
     
        public Term sub(int nr) {
            throw new IndexOutOfBoundsException("Term " + this + " has arity " + arity());
        }
    } 
}









