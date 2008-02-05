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

/** An OpTerm is an object that contains an Operator and several subterms. Can be used
 * to represent e.g., function terms or quantifier terms. Instances should never be 
 * accessed via 
 * this interface, use the interface of the superclass Term and construct instances only via
 * a TermFactory instead.
 */
abstract class OpTerm extends Term {


    public static OpTerm createOpTerm(Operator op, Term[] subs) {        
        if (subs.length == 0) {
            return new ConstantOpTerm(op);
        } else if (subs.length == 1) {
            return new UnaryOpTerm(op, subs);
        } else if (subs.length == 2) {
            return new BinaryOpTerm(op, subs);
        } 
        
        return new ArbitraryOpTerm(op, subs);
    }
    
    public static OpTerm createBinaryOpTerm(Operator op, Term left, Term right) {
        return new BinaryOpTerm(op, new Term[]{left, right});
    }
    
    public static OpTerm createUnaryOpTerm(Operator op, Term sub) {
        return new UnaryOpTerm(op, new Term[]{sub});
    }

    public static OpTerm createConstantOpTerm(Operator op) {
        return new ConstantOpTerm(op);
    }
    
    protected OpTerm(Operator op, Sort sort) {
        super(op, sort);       
        
        if (op instanceof QuantifiableVariable) {
            freeVars = freeVars.add((QuantifiableVariable) op);
        } else if ( op instanceof Metavariable ) {
            metaVars = metaVars.add ( (Metavariable)op );
        }
    }
    
    public ArrayOfQuantifiableVariable varsBoundHere(int n) {
        return EMPTY_VAR_LIST;
    }

    static class ArbitraryOpTerm extends OpTerm {


        private final ArrayOfTerm subTerm;

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

        public int depth() {
            return depth;
        }
    }
     
    static class BinaryOpTerm extends OpTerm {

        private final Term left;
        private final Term right;

        private int depth = -1;
        
        BinaryOpTerm(Operator op, Term[] subs) {
            super(op,op.sort(subs));
            assert subs.length == 2 : "Tried to create a binary term with more or less" +
            " than two sub terms";
            this.left  = subs[0];
            this.right = subs[1];        
            
            fillCaches();
        }
           
        public int arity() {
            return 2;
        }

        public int depth() {
            if (depth == -1) {
                final int leftDepth = left.depth();
                final int rightDepth = right.depth();
                depth = leftDepth > rightDepth ? leftDepth : rightDepth; 
            }
            return depth;
        }

        public Term sub(int nr) {
            if (nr < 0 || nr >= arity()) {
                throw new IndexOutOfBoundsException("Term " + this + " has arity " + arity());
            }
            return nr == 0 ? left : right;
        }
    }

    static class UnaryOpTerm extends OpTerm {

        private final Term sub;

        private int depth = -1;
        
        public UnaryOpTerm(Operator op, Term sub) {
            this(op, new Term[]{sub});
        }
        
        public UnaryOpTerm(Operator op, Term[] subs) {
            super(op,op.sort(subs));
            assert subs.length == 1 : "Tried to create a unary term with more or less" +
                        " than one sub term";
            this.sub  = subs[0];
            fillCaches();
        }
           
        public int arity() {
            return 1;
        }

        public int depth() {
            if (depth == -1) {
                depth = sub.depth() + 1; 
            }
            return depth;
        }

        public Term sub(int nr) {
            if (nr != 0) {
                throw new IndexOutOfBoundsException("Term " + this + " has arity " + arity());
            }
            return sub;
        }       
    }

    static class ConstantOpTerm extends OpTerm {

        private final static Term[] NOSUBS = new Term[0];
        
        public ConstantOpTerm(Operator op) {
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









