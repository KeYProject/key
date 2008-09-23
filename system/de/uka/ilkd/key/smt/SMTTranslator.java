// This file is part of KeY - Integrated Deductive Software Design
package de.uka.ilkd.key.smt;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Vector;

import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.collection.SLListOfString;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.ArrayOp;
import de.uka.ilkd.key.logic.op.AttributeOp;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.IteratorOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Metavariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.op.SetOfMetavariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.decproc.ConstraintSet;
//import de.uka.ilkd.key.proof.decproc.DecisionProcedureSimplifyOp;
import de.uka.ilkd.key.proof.decproc.NumberTranslation;
import de.uka.ilkd.key.proof.decproc.SimplifyException;
import de.uka.ilkd.key.proof.decproc.SimplifyTranslation;
import de.uka.ilkd.key.proof.decproc.UninterpretedTermWrapper;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.java.Services;

import org.apache.log4j.Logger;


/**
 * 
 * @author daniels
 *
 * The class responsible for converting a sequent into the Simplify input language.
 * It is public because ASM-KeY inherits form it to provide a version suppporting
 * asm operators.
 */
public class SMTTranslator { 

        private HashMap cacheForUninterpretedSymbols = null;
        private ListOfString sortAxioms = SLListOfString.EMPTY_LIST;
        private boolean quantifiersOccur=false;   
        private Sort jbyteSort;
        private Sort jshortSort;
        private Sort jintSort;
        private Sort jlongSort;
        private Sort jcharSort;
        private Sort integerSort;
        private static long counter = 0;
        protected static final int ANTECEDENT = 0;
        protected static final int SUCCEDENT = 1;
        protected static final int YESNOT = 2;

        private static String FALSESTRING = "false";
        private static String TRUESTRING = "true";
        private static String ALLSTRING = "forall";
        private static String EXISTSTRING = "exists";
        private static String ANDSTRING = "and";
        private static String ORSTRING = "or";
        private static String NOTSTRING = "not";
        private static String EQSTRING = "=";
        private static String IMPLYSTRING = "implies";
        private static String PLUSSTRING = "+";
        private static String MINUSSTRING = "-";
        private static String MULTSTRING = "*";
        private static String LTSTRING = "<";
        private static String GTSTRING = ">";
        private static String LEQSTRING = "<=";
        private static String GEQSTRING = ">=";
        
        /** The translation result is stored in this variable. */
        protected String text;
        /** StringBuffer contains all declared predicate symbols. */
        protected final StringBuffer predicate = new StringBuffer();
        /** StringBuffer to store text which could be usefull for the user */
        protected final StringBuffer notes = new StringBuffer();
        /** remember all printed predicates */
        protected final Set<Operator> predicateSet = new HashSet<Operator>();
        protected final ArrayList<String> predicatedecls = new ArrayList<String>();
        /** remember all printed functions */
        protected final Set<Operator> functionSet = new HashSet<Operator>();
        protected final Set<Sort> sortSet = new HashSet<Sort>();
        /** remember all function declarations */
        protected final ArrayList<String> functiondecls = new ArrayList<String>();
        /** The Constraint under which the sequent is to be proven */
        protected final ConstraintSet constraintSet;
        
        protected final HashSet usedGlobalMv = new HashSet();
        protected final HashSet usedLocalMv = new HashSet();
        
        protected final SetOfMetavariable localMetavariables;
        protected final HashMap variableMap = new HashMap();
        
        
        /**
         * Just a constructor which starts the conversion to Simplify syntax. The
         * result can be fetched with
         * 
         * @param sequent
         *           The sequent which shall be translated.
         * @param cs
         *           The constraints which shall be incorporated.
         * @param localmv
         *           The local metavariables, should be the ones introduced after
         *           the last branch.
         */
        public SMTTranslator(Sequent sequent, ConstraintSet cs,
                                   SetOfMetavariable localmv, 
                                   Services services,
                                   boolean lightWeight) 
            throws SimplifyException {
//                super(sequent, cs, localmv, services);   
                localMetavariables = localmv;
                constraintSet = cs;
                jbyteSort = services.getTypeConverter().getByteLDT().targetSort();
                jshortSort = services.getTypeConverter().getShortLDT().targetSort();
                jintSort = services.getTypeConverter().getIntLDT().targetSort();
                jlongSort = services.getTypeConverter().getLongLDT().targetSort();
                jcharSort = services.getTypeConverter().getCharLDT().targetSort();
                integerSort = services.getTypeConverter().getIntegerLDT().targetSort();
                cacheForUninterpretedSymbols = new HashMap();
                StringBuffer hb = translate(sequent, lightWeight);
                text = predicate.toString() + produceClosure(hb);
                logger.info("SimplifyTranslation:\n" + text);
                if (notes.length() > 0) {
                        logger.info(notes);
                }
        }

        public SMTTranslator(Sequent sequent, ConstraintSet cs,
                                   SetOfMetavariable localmv, 
                                   Services services) 
                throws SimplifyException {
                this(sequent, cs, localmv, services, false);
        }

        /**
         * For translating only terms and not complete sequents.
         */
        public SMTTranslator(Services s) throws SimplifyException{
                this(null, null, null, s, false);
        }

        /**
         * Goes through the collected metavariables and quantifies them with 
         * universal-quantifieres if they are global and with existential 
         * quantifiers if they are local.
         * @param s The StringBuffer the quantifieres shall be pre- and 
         * the trailing parantheses be appended.
         * @returns The modified StringBuffer as a String.
         */
        protected String produceClosure(StringBuffer s) {
                StringBuffer tmp = new StringBuffer("(");
                tmp.append(ALLSTRING).append(" (");
                for (Iterator i = usedGlobalMv.iterator(); i.hasNext();) {
                        tmp.append(' ').append(
                                        getUniqueVariableName((Metavariable) i.next()));
                }
                tmp.append(")");
                tmp.append("(").append(EXISTSTRING).append(" (");
                for (Iterator i = usedLocalMv.iterator(); i.hasNext();) {
                        tmp.append(' ').append(
                                        getUniqueVariableName((Operator) i.next()));
                }
                tmp.append(")\n ");
                tmp.append(s);
                tmp.append("\n))");
                return tmp.toString();
        }

        protected final StringBuffer translate(Sequent sequent)
                throws SimplifyException {
                return translate(sequent, false);
        }

        private StringBuffer buildDeclarations() {
                //build the sorts
                StringBuffer sorts = new StringBuffer();
                if (sortSet.size() > 0) {
                        sorts.append(":extrasorts (");
                        Iterator<Sort> i = sortSet.iterator();
                        while (i.hasNext()) {
                                Sort curr = i.next();
                                System.out.println("+++++++++++++++++" + curr.toString() + " | " + curr.getClass().toString());
                                sorts.append(" ");
                                sorts.append(curr.name());
                        }
                        sorts.append(" )");
                }
                
                //build the functions
                StringBuffer functions = new StringBuffer();
                if (functiondecls.size() > 0) {
                        functions.append(":extrafuns (");
                        for (int i = 0; i < functiondecls.size(); i++) {
                                functions.append("( ");
                                functions.append(functiondecls.get(i));
                                functions.append(" ) ");
                        }
                        functions.append(")");
                }
                
                //build the predicates
                StringBuffer predicates = new StringBuffer();
                if (predicatedecls.size() > 0) {
                        predicates.append(":extrapreds ( ");
                        for (int i = 0; i < predicatedecls.size(); i++) {
                                predicates.append("( ");
                                predicates.append(predicatedecls.get(i));
                                predicates.append(" ) ");
                        }
                        predicates.append(")");
                }
                
                
                sorts.append("\n");
                sorts.append(functions);
                sorts.append("\n");
                sorts.append(predicates);
                sorts.append("\n");
                        
                return sorts;
        }
        
        /**
         * Translates the given sequent into "Simplify" input syntax and adds the
         * resulting string to the StringBuffer sb.
         * 
         * @param sequent
         *           the Sequent which should be written in Simplify syntax
         */
        protected final StringBuffer translate(Sequent sequent, 
                                               boolean lightWeight)
                        throws SimplifyException {
            //          computeModuloConstraints(sequent);
System.out.println("translate called");                
                StringBuffer hb = new StringBuffer();
                StringBuffer temp;
                hb.append('(').append(IMPLYSTRING).append(' ');
                temp = translate(sequent.antecedent(), ANTECEDENT,
                                lightWeight);
System.out.println("Produced antecedent: " + temp);                
                hb.append(temp);
                hb.append("\n");
                temp = translate(sequent.succedent(), SUCCEDENT,
                                lightWeight);
System.out.println("Produced succedent: " + temp);                 
                hb.append(temp);
                hb.append(')');
                
System.out.println("The declaration used: " + this.buildDeclarations());  

                //build the final StringBuffer
                StringBuffer complete = new StringBuffer("(benchmark KeY\n");
                complete.append(this.buildDeclarations());
                complete.append("\n");
                complete.append(":formula(\n");
                //as universally true is looked for: negate and check for not satisfieable
                complete.append("(not ");
                complete.append(hb);
                complete.append(")");
                complete.append("\n)\n");
                complete.append(")");


/*TODO Maybe uncomment again!
                if (sortAxioms!=SLListOfString.EMPTY_LIST && quantifiersOccur) {
                    String sar[] = sortAxioms.toArray();
                    String axioms=sar[0];
                    for (int i=1; i<sar.length; i++) {
                        axioms="("+DecisionProcedureSimplifyOp.AND+" "+axioms+" "+sar[i]+")";
                    }
                    hb.insert(0, "("+DecisionProcedureSimplifyOp.IMP+" "+axioms);
                    hb.append(')');
                    //System.out.println(axioms);
                }
*/
                return complete;
        }

        protected final StringBuffer translate(Semisequent ss, 
                                               int skolemization)
                throws SimplifyException {
                return translate(ss, skolemization, false);
        }

        /**
         * Translates the given Semisequent into "Simplify" input syntax and adds
         * the resulting string to the StringBuffer sb.
         * 
         * @param semi
         *           the SemiSequent which should be written in Simplify syntax
         */
        protected final StringBuffer translate(Semisequent semi, 
                                               int skolemization,
                                               boolean lightWeight)
                        throws SimplifyException {
                StringBuffer hb = new StringBuffer();
                
                //the semisequence is empty. so return the corresponding formular
                if (semi.size() == 0) {
                        if (skolemization == ANTECEDENT) {
                                hb.append(TRUESTRING);
                        } else {
                                //TODO: verify, if this makes sense!!
                                hb.append(FALSESTRING);
                        }
                        return hb;
                }
                
//              add the conjunctor only if it is really needed!
                if (semi.size() > 1) {
                        hb.append('(');
                        if (skolemization == ANTECEDENT) {
                                hb.append(ANDSTRING);
                        } else {
                                hb.append(ORSTRING);
                        }
                }
                for (int i = 0; i < semi.size(); ++i) {
                        hb.append(' ');
                        hb.append(translate(semi.get(i), lightWeight));
                }
//              if (skolemization == ANTECEDENT) {
//                      hb.append(' ');
//                      hb.append(DecisionProcedureSimplifyOp.LIMIT_FACTS);
//                      hb.append('\n').append(translate(moduloConjoin(), new Vector()));
//              }
                //add the brackets for the conjunctor only if it makes sense
                if (semi.size() > 1)
                        hb.append(')');
                return hb;
        }
        /**
         * Translates the given ConstrainedFormula into "Simplify" input syntax and
         * adds the resulting string to the StringBuffer sb.
         * 
         * @param cf
         *           the ConstrainedFormula which should be written in Simplify
         *           syntax
         *           
         * TODO now: translation out of constraintSet context          
         */
        protected final StringBuffer translate(ConstrainedFormula cf, 
                                               boolean lightWeight)
                throws SimplifyException {
System.out.println("translate ConstrainedFormular");   
System.out.println("current constraint set: " + constraintSet.toString());  
                StringBuffer hb = new StringBuffer();
                Term t;
                //if the cnstraintSet contains cf, make a syntactical replacement
                if (constraintSet.used(cf)) {
System.out.println("translate ConstrainedFormular 2"); 
                        SyntacticalReplaceVisitor srVisitor = 
                                new SyntacticalReplaceVisitor(
                                                constraintSet.chosenConstraint());
                        cf.formula().execPostOrder(srVisitor);
                        t = srVisitor.getTerm();
                } else {
                        t = cf.formula();
                }
                Operator op = t.op();
                if (!lightWeight || !(op instanceof Modality)
                                && !(op instanceof IUpdateOperator)
                                 && !(op instanceof IfThenElse)
                                 && op != Op.ALL
                                 && op != Op.EX){    
System.out.println("translate ConstrainedFormular 3");                                 
                        hb.append(translate(t, new Vector()));
                }
                return hb;
        }
        
        /**
         * Translates the given term into "Simplify" input syntax and adds the
         * resulting string to the StringBuffer sb.
         * 
         * @param term
         *        the Term which should be written in Simplify syntax
         * @param quantifiedVars
         *           a Vector containing all variables that have been bound in
         *           super-terms. It is only used for the translation of modulo
         *           terms, but must be looped through until we get there.
         */
        public final StringBuffer translate(Term term, Vector quantifiedVars) throws SimplifyException {
                Operator op = term.op();
System.out.println("translate called with " + op.toString() + " (Term: "+ term.toString() + " )");
System.out.println("translate of class " + op.getClass().getName());
                if (op == Op.NOT) {
                        return (translateSimpleTerm(term, NOTSTRING, quantifiedVars));
                } else if (op == Op.AND) {
                        return (translateSimpleTerm(term, ANDSTRING, quantifiedVars));
                } else if (op == Op.OR) {
                        return (translateSimpleTerm(term, ORSTRING, quantifiedVars));
                } else if (op == Op.IMP) {
                        return (translateSimpleTerm(term, IMPLYSTRING, quantifiedVars));
                } else if (op == Op.EQV) {
                        return (translateEquiv(term, quantifiedVars));
                } else if (op == Op.EQUALS) {               
                        return (translateSimpleTerm(term,
                                                    EQSTRING, quantifiedVars));
                } else if (op == Op.ALL || op == Op.EX) {
                        quantifiersOccur = true;
                        StringBuffer hb = new StringBuffer();
                        Debug.assertTrue(term.arity() == 1);
                        //append the quantifier symbol
                        hb.append('(').append(
                                        op == Op.ALL
                                                        ? ALLSTRING
                                                        : EXISTSTRING).append(" (");
                        ArrayOfQuantifiableVariable vars = term.varsBoundHere(0);
                        Debug.assertTrue(vars.size()==1);
                        //append the quantified variable including sort
                        String v = translateVariable(vars.getQuantifiableVariable(0)).toString();
                        hb.append(v);
                        hb.append(" " + vars.getQuantifiableVariable(0).sort().name());
                        this.addSort(vars.getQuantifiableVariable(0).sort());
                        Vector cloneVars = (Vector)quantifiedVars.clone(); 
                        collectQuantifiedVars(cloneVars, term);
                        hb.append(") ");
                        
                        /* skip that. unknown why needed
                        // we now add an implication or conjunction of a type predicate if the type is 
                        // different from int
                        
                        hb.append("(").append(
                                              op == Op.ALL
                                              ? IMPLYSTRING
                                              : ANDSTRING);
                        Sort sort = vars.getQuantifiableVariable(0).sort();
                        if (isSomeIntegerSort(sort)) 
                            sort = integerSort;
                        hb.append("("+getUniqueVariableName(sort)+" "+v+" )");
                        addPredicate(getUniqueVariableName(sort).toString(),1);
                        */
                        //append the term
                        hb.append(translate(term.sub(0), cloneVars));                     
                        hb.append(")");
                        
                        return hb;
                } else if (op == Op.TRUE) {
                        return (new StringBuffer(TRUESTRING));
                } else if (op == Op.FALSE) {
                        return (new StringBuffer(FALSESTRING));
                } else if (op instanceof AttributeOp) {
                        return (translateAttributeOpTerm(term, quantifiedVars));
                } else if (op instanceof ProgramMethod) {
                        return (translateSimpleTerm(term, getUniqueVariableName(op)
                                        .toString(), quantifiedVars));
                } else if (op instanceof LogicVariable || op instanceof ProgramVariable) {
                        return (translateVariable(op));
                } else if (op instanceof Metavariable) {
System.out.println("translate Metavariable " + op.toString());                        
                        if (localMetavariables.contains((Metavariable) op)) {
                                usedLocalMv.add(op);
                                System.out.println("Found local mv: " + op.toString());
                        } else {
                                usedGlobalMv.add(op);
                                System.out.println("Found global mv: " + op.toString());
                        }
                        return (translateVariable(op));
                } else if (op instanceof ArrayOp) {
                        return (translateSimpleTerm(term, "ArrayOp", quantifiedVars));
                } else if (op instanceof Function) {
                        String name = op.name().toString().intern();
                        if (name.equals("add")) {
                                return (translateSimpleTerm(term,
                                                PLUSSTRING, quantifiedVars));
                        } else if (name.equals("sub")) {
                                return (translateSimpleTerm(term,
                                                MINUSSTRING, quantifiedVars));
                        } else if (name.equals("neg")) {
                                //%%: This is not really hygienic
                                return (translateUnaryMinus(term,
                                                MINUSSTRING, quantifiedVars));
                        } else if (name.equals("mul")) {
                                return (translateSimpleTerm(term,
                                                MULTSTRING, quantifiedVars));
                        } else if (name.equals("div")) {
                                notes.append(
                                                "Division encountered which is not "
                                                                + "supported by Simplify.").append(
                                                "It is treated as an uninterpreted function.\n");
                                return (translateSimpleTerm(term, getUniqueVariableName(op)
                                                .toString(), quantifiedVars));
                                //                      } 
                                // else if (name.equals("mod")) {
                                //                              Term tt = translateModulo(term, quantifiedVars);
                                //                              if (tt == null) {
                                //                                      return uninterpretedTerm(term, true);
                                //                              } else {
                                //                                      return translate(tt, quantifiedVars);
                                //                              }
                        } else if (name.equals("lt")) {
                                return (translateSimpleTerm(term,
                                                LTSTRING, quantifiedVars));
                        } else if (name.equals("gt")) {
                                return (translateSimpleTerm(term,
                                                GTSTRING, quantifiedVars));
                        } else if (name.equals("leq")) {
                                return (translateSimpleTerm(term,
                                                LEQSTRING, quantifiedVars));
                        } else if (name.equals("geq")) {
                                return (translateSimpleTerm(term,
                                                GEQSTRING, quantifiedVars));
                        } else if (name.equals("Z") || name.equals("C")) {
                                Debug.assertTrue(term.arity() == 1);

                                String res = NumberTranslation.translate(term.sub(0)).toString();
                                final Sort sort;
                                if (isSomeIntegerSort(term.sort())) 
                                        sort = integerSort;
                                else
                                        sort = term.sort();                                
                                String ax = "("+getUniqueVariableName(sort).toString()+" "+res+")";
                                if (!sortAxioms.contains(ax)) {
                                    sortAxioms = sortAxioms.prepend(new String[]{ax});                                    
                                    //addPredicate(getUniqueVariableName(sort).toString(),1);
                                    //addPredicate(term, getUniqueVariableName(sort));
                                    //addSort(sort);
                                }
                                return (new StringBuffer(res));
/* 
// it's sick but if you need to give a demo...
                        } else if (name.equals("short_MIN")) {
                            return new StringBuffer("-32768");
                        } else if (name.equals("short_MAX")) {
                            return new StringBuffer("32767");
                        } else if (name.equals("int_MIN")) {
                            return new StringBuffer("-500000");
                        } else if (name.equals("int_MAX")) {
                            return new StringBuffer("500000");
*/
                        } else if (name.equals("byte_MIN") | name.equals("byte_MAX")
                                        | name.equals("byte_RANGE") | name.equals("byte_HALFRANGE")
                                        | name.equals("short_MIN") | name.equals("short_MAX")
                                        | name.equals("short_RANGE")
                                        | name.equals("short_HALFRANGE") | name.equals("int_MIN")
                                        | name.equals("int_MAX") | name.equals("int_RANGE")
                                        | name.equals("int_HALFRANGE") | name.equals("long_MIN")
                                        | name.equals("long_MAX") | name.equals("long_RANGE")
                                        | name.equals("long_HALFRANGE")) {
                                return (translateSimpleTerm(term, name, quantifiedVars));
                        } else {
                                if (term.sort() == Sort.FORMULA) {
                                        //addPredicate(getUniqueVariableName(op).toString(), op
                                        //                .arity());
                                        addPredicate(term, getUniqueVariableName(op));
                                } else {
                                        addFunction(term, getUniqueVariableName(op));
                                        addSort(term.sort());
                                }
                                
                                
                                return (translateSimpleTerm(term, getUniqueVariableName(op)
                                                .toString(), quantifiedVars));
                        }
                } else if ((op instanceof Modality)
                                || (op instanceof IUpdateOperator)
                                || (op instanceof IfThenElse)) {
                        return (uninterpretedTerm(term, true));
                } else {
                        return (translateUnknown(term));
                }
        }
        
        /**
         * Just copies the quantified variables of term into quantifiedVars
         * @param quantifiedVars
         * @param term
         */
        protected void collectQuantifiedVars (Vector quantifiedVars, Term term) {
                ArrayOfQuantifiableVariable vars = term.varsBoundHere(0);
                for (int i = 0; i < vars.size(); ++i) {
                        quantifiedVars.add(vars.getQuantifiableVariable(i));
                }
        }
        
        /**
         * Takes care of sequent tree parts that were not matched in translate(term,
         * skolemization). In this class it just produces a warning, nothing more.
         * It is provided as a hook for subclasses.
         * 
         * @param term
         *           The Term given to translate
         * @throws SimplifyException
         */
        protected StringBuffer translateUnknown(Term term) throws SimplifyException {
                return (opNotKnownWarning(term));
        }
        
        protected StringBuffer opNotKnownWarning(Term term)
                        throws SimplifyException {
                logger
                                .warn("Warning: unknown operator while translating into Simplify "
                                                + "syntax. Translation to Simplify will be stopped here.\n"
                                                + "opClass="
                                                + term.op().getClass().getName()
                                                + ", opName="
                                                + term.op().name()
                                                + ", sort="
                                                + term.sort().name());
                throw new SimplifyException(term.op().name() + " not known by Simplify");
        }
        
        /**
         * Used to give a variable (program, logic, meta) a unique name.
         * 
         * @param op
         *           The variable to be translated/renamed.
         */
        protected final StringBuffer translateVariable(Operator op) {
System.out.println("translateVariable " + op.toString()); 
//Exception e = new Exception();
//e.printStackTrace();
                StringBuffer res = new StringBuffer("?");
                res.append(getUniqueVariableName(op));
                if (op instanceof ProgramVariable || op instanceof Metavariable) {
                        final Sort sort;
                        if (isSomeIntegerSort(op.sort(null))) 
                                sort = integerSort;
                        else
                                sort = op.sort(null);
                        String ax = "("+getUniqueVariableName(sort).toString()+" "+res+")";
//TODO: needed??
//                        if (!sortAxioms.contains(ax)) {
//                                sortAxioms = sortAxioms.prepend(new String[]{ax});                                                       
//                                //addPredicate(getUniqueVariableName(sort).toString(),1); 
//                        }
                }
                return res;
        }
        
        
        
        /**
         * produces a unique name for the given Variable, enclosed in '|' and with a
         * unique hashcode.
         * 
         * @param op
         *           The variable to get a new name.
         */
        protected final StringBuffer getUniqueVariableName(Named op) {
            String name = op.name().toString();
            if(name.indexOf("undef(") != -1){
                name = "_undef";
            }
            if(name.indexOf("::")==-1 && name.indexOf(".")==-1 && 
               name.indexOf("-")==-1 && !name.startsWith("_") &&
               name.indexOf("[")==-1 && name.indexOf("]")==-1){
                return new StringBuffer(name).
                    append("_").append(getUniqueHashCode(op));
            }
            return new StringBuffer("|").
                append(name).
                append("_").append(getUniqueHashCode(op)).append("|");
        }
        
        protected final StringBuffer uninterpretedTerm(Term term,
                        boolean modRenaming) {
            if (cacheForUninterpretedSymbols.containsKey(term))
                return (StringBuffer)cacheForUninterpretedSymbols.get(term);
            StringBuffer hb = new StringBuffer();
            StringBuffer temp = new StringBuffer();
            temp.append('|').append(term.op().name()).append('_');
            if (modRenaming) {
                temp.append(getUniqueHashCodeForUninterpretedTerm(term));
            } else {
                temp.append(getUniqueHashCode(term));
            }
            temp.append('|');
            hb.append(temp);
            IteratorOfQuantifiableVariable i;
            for (i = term.freeVars().iterator(); i.hasNext();) {
                hb.append(' ');
                hb.append(translateVariable(i.next()));
            }

            if (term.sort() != Sort.FORMULA) {
                String ax;
                final Sort sort;
                if (isSomeIntegerSort(term.sort())) 
                        sort = integerSort;
                else
                        sort = term.sort();
                addSort(term.sort());
                
                if (term.arity() > 0)
                    ax = "("+getUniqueVariableName(sort).toString()+" ("+hb+"))";
                else
                    ax = "("+getUniqueVariableName(sort).toString()+" "+hb+")";
                if (!sortAxioms.contains(ax)) {
                    sortAxioms = sortAxioms.prepend(new String[]{ax});                                                        
                    //addPredicate(getUniqueVariableName(sort).toString(),1);
                    addPredicate(term, getUniqueVariableName(sort)); 
                }
            }

            hb.insert(0,'(');
            hb.append(')');

            if (term.sort() == Sort.FORMULA)
                //addPredicate(temp.toString(), term.freeVars().size());
            addPredicate(term, temp);        
            cacheForUninterpretedSymbols.put(term, hb);
            return hb;
        }
    /**
     * Takes a term and translates it with its argument in the Simplify syntax.
     * 
     * @param term
     *           The term to be converted.
     * @param name
     *           The name that should be used for the term (should be unique,
     *           it should be taken care of that somewhere else (if desired)).
     * @param quantifiedVars
     *           a Vector containing all variables that have been bound in
     *           super-terms. It is only used for the translation of modulo
     *           terms, but must be looped through until we get there.
     */
    protected final StringBuffer translateSimpleTerm(Term term, String name, Vector quantifiedVars)
        throws SimplifyException {
        StringBuffer hb = new StringBuffer();
        //don't add brackets, if a constant is delivered
        if (term.arity() > 0)
                hb.append('(');
                
        hb.append(name);
        StringBuffer res = null;
        for (int i = 0; i < term.arity(); ++i) {
            Debug.assertTrue(term.varsBoundHere(i).size() == 0);
            hb.append(' ');
            res = translate(term.sub(i), quantifiedVars);
            if (res!=null && term.sub(i).sort()!=Sort.FORMULA) {
                final Sort sort;
                if (isSomeIntegerSort(term.sub(i).sort())) 
                        sort = integerSort;
                else
                        sort = term.sub(i).sort();
                addSort(sort);
                String ax = "("+getUniqueVariableName(sort).toString()+" "+res+")";
//TODO needed?
//                if (!sortAxioms.contains(ax)) {
//                    sortAxioms = sortAxioms.prepend(new String[]{ax});                                                        
//                    //addPredicate(getUniqueVariableName(sort).toString(),1);
//                    addPredicate(term, getUniqueVariableName(sort)); 
//                }
            }
            
            hb.append(res);
        }
        //don't add brackets, if a constant is delivered
        if (term.arity() > 0)
        hb.append(')');

        // add sort axioms
        return hb;
    }
    
    /**
     * Takes an equivalence term and translates it with its argument in the Simplify syntax.
     * 
     * @param term
     *           The term to be converted.
     * @param quantifiedVars
     *           a Vector containing all variables that have been bound in
     *           super-terms. It is only used for the translation of modulo
     *           terms, but must be looped through until we get there.
     */
    protected final StringBuffer translateEquiv(Term term, Vector quantifiedVars)
        throws SimplifyException {
        
        //the first argument
        StringBuffer left = null;
        Debug.assertTrue(term.varsBoundHere(0).size() == 0);
            
        left = translate(term.sub(0), quantifiedVars);
        if (left!=null && term.sub(0).sort()!=Sort.FORMULA) {
                final Sort sort;
                if (isSomeIntegerSort(term.sub(0).sort())) 
                        sort = integerSort;
                else
                        sort = term.sub(0).sort();
                addSort(sort);
                String ax = "("+getUniqueVariableName(sort).toString()+" "+left+")";
//TODO needed?
//                if (!sortAxioms.contains(ax)) {
//                    sortAxioms = sortAxioms.prepend(new String[]{ax});                                                        
//                    //addPredicate(getUniqueVariableName(sort).toString(),1);
//                    addPredicate(term, getUniqueVariableName(sort)); 
//                }
        }
        
//      the second argument
        StringBuffer right = null;
        Debug.assertTrue(term.varsBoundHere(1).size() == 0);
            
        right = translate(term.sub(1), quantifiedVars);
        if (right!=null && term.sub(1).sort()!=Sort.FORMULA) {
                final Sort sort;
                if (isSomeIntegerSort(term.sub(1).sort())) 
                        sort = integerSort;
                else
                        sort = term.sub(1).sort();
                addSort(sort);
                String ax = "("+getUniqueVariableName(sort).toString()+" "+left+")";
//TODO needed?
//                if (!sortAxioms.contains(ax)) {
//                    sortAxioms = sortAxioms.prepend(new String[]{ax});                                                        
//                    //addPredicate(getUniqueVariableName(sort).toString(),1);
//                    addPredicate(term, getUniqueVariableName(sort)); 
//                }
        }
        
        StringBuffer hb = new StringBuffer();

        hb.append('(');        
                hb.append(ANDSTRING);
                hb.append(" ");
        
                hb.append("(");
                        hb.append(IMPLYSTRING);
                        hb.append(' ');
                                hb.append(left);
                                hb.append(' ');
                                hb.append(right);
        
                hb.append(") (");
                hb.append(IMPLYSTRING);
                hb.append(' ');
                        hb.append(right);
                        hb.append(' ');
                        hb.append(left);

                hb.append(')');
        
        hb.append(')'); 

        // add sort axioms
        return hb;
    }
    
    /**
     * Takes an AttributeOp and translates it into the Simplify syntax.
     * 
     * @param term
     *           The term to be converted.
     * @param quantifiedVars
     *           a Vector containing all variables that have been bound in
     *           super-terms. It is only used for the translation of modulo
     *           terms, but must be looped through until we get there.
     */
    protected final StringBuffer translateAttributeOpTerm(Term term, Vector quantifiedVars)
        throws SimplifyException {
System.out.println("translateAttributeTerm " + term.op().toString());            
        StringBuffer hb = new StringBuffer();
        if (logger.isDebugEnabled()) {
            logger.debug("opClass=" + term.op().getClass().getName()
                         + ", opName=" + term.op().name() + ", sort="
                         + term.sort().name());
        }

        hb.append(getUniqueVariableName(term.op()));
        Debug.assertTrue(term.varsBoundHere(0).size() == 0);
        hb.append(' ');
        hb.append(translate(term.sub(0), quantifiedVars));
        hb.insert(0,'(');
        hb.append(')'); 

        final Sort sort;
        if (isSomeIntegerSort(term.sort())) 
                sort = integerSort;
        else
                sort = term.sort();
        addSort(sort);
        String ax = "("+getUniqueVariableName(sort).toString()+" "+hb+")";
        if (!sortAxioms.contains(ax)) {
            sortAxioms = sortAxioms.prepend(new String[]{ax});                                                
            //addPredicate(getUniqueVariableName(sort).toString(),1);
            addPredicate(term, getUniqueVariableName(sort));
        }

        return hb;
    }
    /**
     * Translates the unary minus ~m into a "0 -" construct. Could be solved
     * better with a newly created term!!!
     * 
     * @param term
     *           The term to be converted.
     * @param name
     *           The name that should be used for the term (should be unique,
     *           it should be taken care of that somewhere else (if desired)).
     * @param quantifiedVars
     *           a Vector containing all variables that have been bound in
     *           super-terms. It is only used for the translation of modulo
     *           terms, but must be looped through until we get there.
     */
    protected final StringBuffer translateUnaryMinus(Term term, String name, Vector quantifiedVars)
        throws SimplifyException {
        StringBuffer hb = new StringBuffer();
        hb.append('(').append(name).append(" 0 ");
        hb.append(translate(term.sub(0), quantifiedVars));
        hb.append(')');
        return hb;
    }
    
    /**
     * Adds a predicate to the internal set and adds a line to declare the
     * predicate to the declarator stringbuffer.
     * 
     * @param name
     *           The name of the predicate (no KeY representation jas to
     *           exist).
     * @param term
     *           The arity of the term.
     *           
     * TODO: fix javadoc          
     */
    /*protected final void addPredicate(String name, int arity) {
        if (!predicateSet.contains(name)) {
            predicateSet.add(name);
            predicate.append("(DEFPRED (").append(name);
            for (int i = 0; i < arity; ++i) {
                predicate.append(" x").append(counter++);
            }
            predicate.append("))\n");
        }
    }*/
    protected final void addPredicate(Term term, StringBuffer name) {
            if (!predicateSet.contains(term.op())) {
                    Exception e = new Exception();
                    e.printStackTrace();
                predicateSet.add(term.op());
                StringBuffer temp = new StringBuffer(name).append(" ");
                for (int i = 0; i < term.arity(); i++) {
                        temp.append(term.sub(i).sort().name());
                        temp.append(" ");
                }
                predicatedecls.add(temp.toString());
            }
        }
    
    
        /**
         * Adds a function to the internal set.
         * 
         * @param term
         *           The term that represents the function
         *           
         * @param name
         *           The functions.
         */
        protected final void addFunction(Term term, StringBuffer name) {
                if (!functionSet.contains(term.op())) {
                        functionSet.add(term.op());
                        StringBuffer temp = new StringBuffer(name).append(" "); 
                        temp.append(term.sort().name());
                        for (int i = 0; i < term.arity(); i++) {
                                temp.append(" ");
                                temp.append(term.sub(i).sort().name());
                        }
                        functiondecls.add(temp.toString());
                }
        }
        
        /**
         * Adds a function to the internal set.
         * 
         * @param s
         *           The sort that was found
         *           
         */
        protected final void addSort(Sort s) {
                if (!(s.name().toString().equals("int")) && !sortSet.contains(s)) {
                        sortSet.add(s);
                }
        }
    
    /**
     * For some terms (AttributeOps) the order in KeY is different than the
     * order of the user or Simplify expects.
     * 
     * @return the simplified version of the Term t in reversed order
     * @param t
     *           the Term which should be written in Simplify syntax, but in
     *           reverse order compared to the internal order in KeY
     */
    protected final StringBuffer printlastfirst(Term t) {
        StringBuffer sbuff = new StringBuffer();
        if (t.op().arity() > 0) {
            Debug.assertTrue(t.op().arity() == 1);
            sbuff.append(printlastfirst(t.sub(0)));
            //sbuff.append('.');
        }
        sbuff.append(t.op().name()).append("\\|").append(
                                                         getUniqueHashCode(t.op()));
        return sbuff;
    }
    
    
    static Logger logger = Logger.getLogger(SimplifyTranslation.class.getName());
    
    
    /** 
     * Used just to be called from DecProcTranslation
     * @see de.uka.ilkd.key.proof.decproc.DecProcTranslation#translate(Semisequent, int)
     */
    protected final StringBuffer translate(Term term, int skolemization, Vector quantifiedVars) throws SimplifyException {
        return translate(term, quantifiedVars);
    }
    
    private boolean isSomeIntegerSort(Sort s) {
        if (s == jbyteSort ||
                s == jshortSort ||
                s == jintSort ||
                s == jlongSort ||
                s == jcharSort )
            return true;
        return false;
    }
    
        /**
         * Returns a unique HashCode for the object qv.
         * Unique means unique for the goal given to the calling class.
         * This function does not depend on .hashcode() to deliver unique 
         * hash codes like the memory address of the object. It uses a 
         * hashMap and compares every new Object in O(n) (n number of 
         * Objects with the same .hashCode()) to all others.
         * @param qv the Object the hashcode should be returned.
         * @returns a unique hashcode for the variable gv.
         */
        public int getUniqueHashCode(Object qv) {
                Integer number = (Integer) this.variableMap.get(qv);
                if (number == null) {
                        number = new Integer(this.variableMap.size());
                        this.variableMap.put(qv, number);
                }
                return number.intValue();
        }
        
        /**
         * Returns a unique HashCode for the term qv.
         * Unique means unique for the goal given to the calling class.
         * This function does not depend on .hashcode() to deliver 
         * unique hash codes like the memory address of the object. 
         * It uses a hashMap and compares
         * every new Object in O(n) (n number of Objects 
         * with the same .hashCode()) to all others.
         * It compares with .equalsModRenaming().
         * @returns a unique hashcode for the term gv.
         * @param term the Term the hashcode should be returned.
         */
        public int getUniqueHashCodeForUninterpretedTerm(Term term) {
                Integer number = (Integer) this.variableMap
                                .get(new UninterpretedTermWrapper(term));
                if (number == null) {
                        number = new Integer(this.variableMap.size());
                        this.variableMap.put(new UninterpretedTermWrapper(term), number);
                }
                return number.intValue();
        }
}
