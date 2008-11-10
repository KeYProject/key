package de.uka.ilkd.key.smt;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Vector;

import javax.swing.text.html.HTMLDocument.HTMLReader.IsindexAction;

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

public abstract class AbstractSmtTranslator {
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
        
        /** The translation result is stored in this variable. */
        protected String text;
        /** StringBuffer contains all declared predicate symbols. */
        protected final StringBuffer predicate = new StringBuffer();
        /** StringBuffer to store text which could be usefull for the user */
        protected final StringBuffer notes = new StringBuffer();
        /** remember all printed predicates */
        protected final Set<Operator> predicateSet = new HashSet<Operator>();
//        protected final ArrayList<String> predicatedecls = new ArrayList<String>();
        /** remember all printed functions */
        protected final Set<Operator> functionSet = new HashSet<Operator>();
        protected final Set<Sort> sortSet = new HashSet<Sort>();
        /** remember all function declarations */
//        protected final ArrayList<String> functiondecls = new ArrayList<String>();
        /** The Constraint under which the sequent is to be proven */
        protected final ConstraintSet constraintSet;
        
        protected final HashSet usedGlobalMv = new HashSet();
        protected final HashSet usedLocalMv = new HashSet();
        
        protected final SetOfMetavariable localMetavariables;
        protected final HashMap variableMap = new HashMap();
        
        
        private HashMap<Operator, ArrayList<Sort>> functionDecls = new HashMap<Operator, ArrayList<Sort>>();
        private HashMap<Operator, ArrayList<Sort>> predicateDecls = new HashMap<Operator, ArrayList<Sort>>();
        private HashSet<Sort> usedSorts = new HashSet<Sort>();
        private HashMap<Operator, StringBuffer> usedVariableNames = new HashMap<Operator, StringBuffer>();
        private HashMap<Operator, StringBuffer> usedFunctionNames = new HashMap<Operator, StringBuffer>();
        private HashMap<Operator, StringBuffer> usedPredicateNames = new HashMap<Operator, StringBuffer>();
        private HashMap<Sort, StringBuffer> usedDisplaySort = new HashMap<Sort, StringBuffer>();
        private HashMap<Sort, StringBuffer> usedRealSort = new HashMap<Sort, StringBuffer>();
        private HashMap<Sort, StringBuffer> typePredicates = new HashMap<Sort, StringBuffer>();
        //used type predicates for constant values, e.g. 1, 2, ...
        private HashMap<Term, StringBuffer> constantTypePreds = new HashMap<Term, StringBuffer>();
        
        
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
        public AbstractSmtTranslator(Sequent sequent, ConstraintSet cs,
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
                StringBuffer hb = translate(sequent, lightWeight, services);
//                text = predicate.toString() + produceClosure(hb);
//                text = predicate.toString();
//                logger.info("SimplifyTranslation:\n" + text);
//                if (notes.length() > 0) {
//                        logger.info(notes);
//                }
        }

        public AbstractSmtTranslator(Sequent sequent, ConstraintSet cs,
                                   SetOfMetavariable localmv, 
                                   Services services) 
                throws SimplifyException {
                this(sequent, cs, localmv, services, false);
        }

        /**
         * For translating only terms and not complete sequents.
         */
        public AbstractSmtTranslator(Services s) throws SimplifyException{
                this(null, null, null, s, false);
        }


        protected final StringBuffer translate(Sequent sequent, Services services)
                throws SimplifyException {
                return translate(sequent, false, services);
        }

        
        /**
         * Translates the given sequent into "Simplify" input syntax and adds the
         * resulting string to the StringBuffer sb.
         * 
         * @param sequent
         *           the Sequent which should be written in Simplify syntax
         */
        protected final StringBuffer translate(Sequent sequent, 
                                               boolean lightWeight,
                                               Services services)
                        throws SimplifyException {
            //          computeModuloConstraints(sequent); 
                
                //translate
                StringBuffer hb = new StringBuffer();
                StringBuffer ante;
//                hb.append('(').append(IMPLYSTRING).append(' ');
                ante = translate(sequent.antecedent(), ANTECEDENT,
                                lightWeight, services);               
//                hb.append(temp);
//                hb.append("\n");
                StringBuffer succ;
                succ = translate(sequent.succedent(), SUCCEDENT,
                                lightWeight, services);                
//                hb.append(temp);
//                hb.append(')');
                 
                //append type definitions, if neccessary
                ante = this.translateLogicalAnd(this.getTypeDefinitions(), ante);
                
                hb = this.translateLogicalImply(ante, succ);
                hb = this.translateLogicalNot(hb);

                return buildCompleteText(hb, this.buildTranslatedFuncDecls()
                                , this.buildTranslatedPredDecls(), this.buildTranslatedSorts());
        }
        
        private StringBuffer getTypeDefinitions() {
                StringBuffer toReturn;
                toReturn = this.translateLogicalTrue();
                
                //add the type definitions fo functions
                for (Operator op : functionDecls.keySet()) {
                        StringBuffer currentForm = this.getSingleFunctionDef(
                                        this.usedFunctionNames.get(op), functionDecls.get(op));
                        toReturn = this.translateLogicalAnd(currentForm, toReturn);
                }
                
                //add the type definitions for constant values
                for (StringBuffer s : this.constantTypePreds.values()) {
                        toReturn = this.translateLogicalAnd(s, toReturn);
                }
                
                
                return toReturn;
        }
        
        private StringBuffer getSingleFunctionDef(StringBuffer funName, ArrayList<Sort> sorts) {
                StringBuffer toReturn = new StringBuffer();
                
                //collect the quantify vars
                ArrayList<StringBuffer> qVar = new ArrayList<StringBuffer>();
                for (int i = 0; i < sorts.size()-1; i++){
                        qVar.add(this.translateLocicalVar(new StringBuffer("tvar")));
                }
                
                //left hand side of the type implication
                if (qVar.size() > 0) {
                        toReturn = this.getTypePredicate(sorts.get(0), qVar.get(0));
                }
                for (int i = 1; i < qVar.size(); i++) {
                        StringBuffer temp = getTypePredicate(sorts.get(1), qVar.get(1));
                        toReturn = this.translateLogicalAnd(toReturn, temp);
                }
                
                //build the right side
                StringBuffer rightSide;
                rightSide = this.translateFunction(funName, qVar);
                rightSide = getTypePredicate(sorts.get(sorts.size()-1), rightSide);
                
                if (qVar.size() > 0) {
                        toReturn = this.translateLogicalImply(toReturn, rightSide);
                } else {
                        toReturn = rightSide;
                }
                
                //built the forall around it
                for (int i = qVar.size()-1; i >= 0; i--) {
                        this.translateLogicalAll(qVar.get(i)
                                        , this.usedDisplaySort.get(sorts.get(i))
                                        , toReturn);
                }
                
                return toReturn;
        }

        /**
         * Build the translated function declarations.
         * Each element in the ArrayList represents (functionname | argType1 | ... | argTypen| resultType)
         * @return structured List of declaration.
         */
        private ArrayList<ArrayList<StringBuffer>> buildTranslatedFuncDecls() {
                ArrayList<ArrayList<StringBuffer>> toReturn = new ArrayList<ArrayList<StringBuffer>>();
                for (Operator op : this.functionDecls.keySet()) {
                        ArrayList<StringBuffer> element = new ArrayList<StringBuffer>();
                        element.add(usedFunctionNames.get(op));
                        for (Sort s : functionDecls.get(op)) {
                                element.add(usedDisplaySort.get(s));
                        }
                        toReturn.add(element);
                }
                return  toReturn;
        }
        
        /**
         * Build the translated predicate declarations.
         * Each element in the ArrayList represents (functionname | argType1 | ... | argTypen)
         * @return structured List of declaration.
         */
       private ArrayList<ArrayList<StringBuffer>> buildTranslatedPredDecls() {               
                ArrayList<ArrayList<StringBuffer>> toReturn = new ArrayList<ArrayList<StringBuffer>>();
                //add the predicates
                for (Operator op : this.predicateDecls.keySet()) {
                        ArrayList<StringBuffer> element = new ArrayList<StringBuffer>();
                        element.add(usedPredicateNames.get(op));
                        for (Sort s : predicateDecls.get(op)) {
                                element.add(usedDisplaySort.get(s));
                        }
                        toReturn.add(element);
                }
                
                //add the typePredicates
                if (!this.isMultiSorted()) {
                        for (Sort s : this.typePredicates.keySet()) {
                                ArrayList<StringBuffer> element = new ArrayList<StringBuffer>();
                                element.add(typePredicates.get(s));
                                element.add(this.usedDisplaySort.get(s));
                                toReturn.add(element);
                        }
                }
                return  toReturn;
        }
        
       /**
        * ArrayList of all sorts, that were used as sorts.
        * Including the integer sort.
        * @return ArrayList of the names of sorts.
        */
        private ArrayList<StringBuffer> buildTranslatedSorts() { 
                ArrayList<StringBuffer> toReturn = new ArrayList<StringBuffer>();
                for (Sort s : this.usedDisplaySort.keySet()) {
                        StringBuffer newSort = this.usedDisplaySort.get(s);
                        //make sure, no sort is added twice!!
                        boolean alreadyIn = false;
                        for (int i = 0; !alreadyIn && i < toReturn.size(); i++) {
                                if (toReturn.get(i).equals(newSort));
                        }
                        if (!alreadyIn) {
                                toReturn.add(newSort);
                        }
                }
                return toReturn;
        }        
        
        /**
         * Build the text, that can be read by the final decider.
         * @param formula The formula, that was built out of the internal representation.
         * @param functions List of functions. 
         *      Each Listelement is built up like (name | sort1 | ... | sortn | resultsort)
         * @param predicates List of predicates. 
         *      Each Listelement is built up like (name | sort1 | ... | sortn)
         * @param types List of the used types.
         * @return The Stringbuffer that can be read by the decider
         */
        public abstract StringBuffer buildCompleteText(StringBuffer formula
                        , ArrayList<ArrayList<StringBuffer>> functions
                        , ArrayList<ArrayList<StringBuffer>> predicates
                        , ArrayList<StringBuffer> types);
        
        protected final StringBuffer translate(Semisequent ss, 
                                               int skolemization,
                                               Services services)
                throws SimplifyException {
                return translate(ss, skolemization, false, services);
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
                                               boolean lightWeight,
                                               Services services)
                        throws SimplifyException {
                StringBuffer hb = new StringBuffer();
                
                //the semisequence is empty. so return the corresponding formular
                if (semi.size() == 0) {
                        if (skolemization == ANTECEDENT) {
                                hb.append(translateLogicalTrue());
                        } else {
                                hb.append(translateLogicalFalse());
                        }
                        return hb;
                }
                
//              add the conjunctor only if it is really needed!
//                if (semi.size() > 1) {
//                        hb.append('(');
//                        if (skolemization == ANTECEDENT) {
//                                hb.append(ANDSTRING);
//                        } else {
//                                hb.append(ORSTRING);
//                        }
//                }
                for (int i = 0; i < semi.size(); ++i) {
                        if (skolemization == ANTECEDENT) {
                                hb = translateLogicalAnd(hb, translate(semi.get(i), lightWeight, services));
                        } else {
                                hb = translateLogicalOr(hb, translate(semi.get(i), lightWeight, services));
                        }
                        //hb.append(' ');
                        //hb.append(translate(semi.get(i), lightWeight, services));
                }
//              if (skolemization == ANTECEDENT) {
//                      hb.append(' ');
//                      hb.append(DecisionProcedureSimplifyOp.LIMIT_FACTS);
//                      hb.append('\n').append(translate(moduloConjoin(), new Vector()));
//              }
                //add the brackets for the conjunctor only if it makes sense
//               if (semi.size() > 1)
//                        hb.append(')');

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
         */
        protected final StringBuffer translate(ConstrainedFormula cf, 
                                               boolean lightWeight, Services services)
                throws SimplifyException { 
                StringBuffer hb = new StringBuffer();
                Term t;
                //if the cnstraintSet contains cf, make a syntactical replacement
                if (constraintSet.used(cf)) {
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
                        hb.append(translate(t, new Vector(), services));
                }
                return hb;
        }
        
        /**
         * Returns, wheather the Structer, this translator creates should be a Structur,
         * that is multi sorted with inheritance of Sorts. If false, a single sorted
         * structure is created.
         * @return true, if multi sorted logic is supported.
         */
        public abstract boolean isMultiSorted();
        
        /**
         * The String used for integer values.
         * This sort is also used in single sorted logics.
         * @return The String used for integers.
         */
        public abstract StringBuffer getIntegerSort();
        
        /**
         * Build the Stringbuffer for a logical NOT.
         * @param arg The Formula to be negated.
         * @return The StringBuffer representing the resulting Formular
         */
        public abstract StringBuffer translateLogicalNot(StringBuffer arg);
        
        /**
         * Build the logical konjunction.
         * @param arg1 The first formula.
         * @param arg2 The second formula.
         * @return The StringBuffer representing the resulting formular.
         */
        public abstract StringBuffer translateLogicalAnd(StringBuffer arg1, StringBuffer arg2);
        
        /**
         * Build the logical disjunction.
         * @param arg1 The first formula.
         * @param arg2 The second formula.
         * @return The StringBuffer representing the resulting formular.
         */
        public abstract StringBuffer translateLogicalOr(StringBuffer arg1, StringBuffer arg2);

        /**
         * Build the logical implication.
         * @param arg1 The first formula.
         * @param arg2 The second formula.
         * @return The StringBuffer representing the resulting formular
         */
        public abstract StringBuffer translateLogicalImply(StringBuffer arg1, StringBuffer arg2);

        /**
         * Build the logical equivalence.
         * @param arg1 The first formula.
         * @param arg2 The second formula.
         * @return The StringBuffer representing the resulting formular
         */
        public abstract StringBuffer translateLogicalEquivalence(StringBuffer arg1, StringBuffer arg2);

        /**
         * Build the logical forall formula.
         * @param var the bounded variable.
         * @param type the type of the bounded variable.
         * @param form The formula containing the bounded variable.
         * @return The resulting formula.
         */
        public abstract StringBuffer translateLogicalAll(StringBuffer var, StringBuffer type, StringBuffer form);

        /**
         * Build the logical exists formula.
         * @param var the bounded variable.
         * @param type the type of the bounded variable.
         * @param form The formula containing the bounded variable.
         * @return The resulting formula.
         */
        public abstract StringBuffer translateLogicalExist(StringBuffer var, StringBuffer type, StringBuffer form);

        /**
         * Translate the logical true.
         * @return The StringBuffer the logical true value.
         */
        public abstract StringBuffer translateLogicalTrue();

        /**
         * Translate the logical false.
         * @return The StringBuffer the logical false value.
         */
        public abstract StringBuffer translateLogicalFalse();
        
        /**
         * Build the Stringbuffer for an object equivalence.
         * @param arg1 The first formula of the equivalence.
         * @param arg2 The second formula of the equivalence.
         * @return The StringBuffer representing teh resulting Formular
         */
        public abstract StringBuffer translateObjectEqual(StringBuffer arg1, StringBuffer arg2);

        /**
         * Build the Stringbuffer for an variable.
         * @return The StringBuffer representing the resulting Formular
         */
        public abstract StringBuffer translateLocicalVar(StringBuffer name);

        /**
         * Build the Stringbuffer for an constant.
         * @return The StringBuffer representing the resulting Formular
         */
        public abstract StringBuffer translateLocicalConstant(StringBuffer name);
        
        /**
         * Translate a predicate.
         * @param name The Symbol of the predicate.
         * @param args The arguments of the predicate.
         * @return the formula representing the predicate.
         */
        public abstract StringBuffer translatePredicate(StringBuffer name, ArrayList<StringBuffer> args);
        
        /**
         * Get the name for a predicate symbol.
         * @param name The name that can be used to create the symbol.
         * @return The unique predicate symbol.
         */
        public abstract StringBuffer translatePredicateName(StringBuffer name);
        
        /**
         * Translate a function.
         * @param name The Symbol of the function.
         * @param args The arguments of the function.
         * @return the formula representing the function.
         */
        public abstract StringBuffer translateFunction(StringBuffer name, ArrayList<StringBuffer> args);
        
        /**
         * Get the name for a function symbol.
         * @param name The name that can be used to create the symbol.
         * @return The unique function symbol.
         */
        public abstract StringBuffer translateFunctionName(StringBuffer name);
        
        /**
         * Translate the integer plus.
         * @param arg1 first val of the sum.
         * @param arg2 second val of the sum.
         * @return The formula representing the integer plus.
         */
        public abstract StringBuffer translateIntegerPlus(StringBuffer arg1, StringBuffer arg2);
        
        /**
         * Translate the integer minus.
         * @param arg1 The first val of the substraction.
         * @param arg2 second val of the substraction.
         * @return The formula representing the integer substraction.
         */
        public abstract StringBuffer translateIntegerMinus(StringBuffer arg1, StringBuffer arg2);
        
        /**
         * Translate a unary minus.
         * @param arg the argument of the unary minus.
         * @return the formula representing tha unary minus function.
         */
        public abstract StringBuffer translateIntegerUnaryMinus(StringBuffer arg);
        
        /**
         * Translate the integer multiplication.
         * @param arg1 The first val of the multiplication.
         * @param arg2 second val of the multiplication.
         * @return The formula representing the integer multiplication.
         */
        public abstract StringBuffer translateIntegerMult(StringBuffer arg1, StringBuffer arg2);
        
        /**
         * Translate the integer division.
         * @param arg1 The first val of the division.
         * @param arg2 second val of the division.
         * @return The formula representing the integer division.
         */
        public abstract StringBuffer translateIntegerDiv(StringBuffer arg1, StringBuffer arg2);
        
        /**
         * Translate the integer modulo.
         * @param arg1 The first val of the modulo.
         * @param arg2 second val of the modulo.
         * @return The formula representing the integer modulo.
         */
        public abstract StringBuffer translateIntegerMod(StringBuffer arg1, StringBuffer arg2);
        
        /**
         * Translate the greater than.
         * @param arg1 The first val of the greater than.
         * @param arg2 second val of the greater than.
         * @return The formula representing the greater than.
         */
        public abstract StringBuffer translateIntegerGt(StringBuffer arg1, StringBuffer arg2);
        
        /**
         * Translate the less than.
         * @param arg1 The first val of the less than.
         * @param arg2 second val of the less than.
         * @return The formula representing the less than.
         */
        public abstract StringBuffer translateIntegerLt(StringBuffer arg1, StringBuffer arg2);
        
        /**
         * Translate the greater or equal.
         * @param arg1 The first val of the greater or equal.
         * @param arg2 second val of the greater or equal.
         * @return The formula representing the greater or equal.
         */
        public abstract StringBuffer translateIntegerGeq(StringBuffer arg1, StringBuffer arg2);
        
        /**
         * Translate the less or equal.
         * @param arg1 The first val of the less or equal.
         * @param arg2 second val of the less or equal.
         * @return The formula representing the less or equal.
         */
        public abstract StringBuffer translateIntegerLeq(StringBuffer arg1, StringBuffer arg2);
        
        /**
         * Translate a sort.
         * 
         * @param name the sorts name
         * @param isIntVal true, if the sort should represent some kind of integer
         * 
         * @return The String used for this sort. If Multisorted in Declarations, 
         *      esle for the typepredicates.
         */
        public abstract StringBuffer translateSort(String name, boolean isIntVal);
        
        
        /**
         * Translate a sort. Return the StringBuffer, that should be displayed at definitionpart.
         * i.e. the name used for typepredicates an similair.
         * 
         * @return the sorts name
         */
        public abstract StringBuffer translateIntegerValue(long val);
        
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
        public final StringBuffer translate(Term term, Vector quantifiedVars, Services services) throws SimplifyException {
                Operator op = term.op();
                if (op == Op.NOT) {
                        StringBuffer arg = translate(term.sub(0), quantifiedVars, services);
                        return this.translateLogicalNot(arg);
                } else if (op == Op.AND) {
                        StringBuffer arg1 = translate(term.sub(0), quantifiedVars, services);
                        StringBuffer arg2 = translate(term.sub(1), quantifiedVars, services);
                        return this.translateLogicalAnd(arg1, arg2);
                } else if (op == Op.OR) {
                        StringBuffer arg1 = translate(term.sub(0), quantifiedVars, services);
                        StringBuffer arg2 = translate(term.sub(1), quantifiedVars, services);
                        return this.translateLogicalOr(arg1, arg2);
                } else if (op == Op.IMP) {
                        StringBuffer arg1 = translate(term.sub(0), quantifiedVars, services);
                        StringBuffer arg2 = translate(term.sub(1), quantifiedVars, services);
                        return this.translateLogicalImply(arg1, arg2);
                } else if (op == Op.EQV) {
                        StringBuffer arg1 = translate(term.sub(0), quantifiedVars, services);
                        StringBuffer arg2 = translate(term.sub(1), quantifiedVars, services);
                        return this.translateLogicalEquivalence(arg1, arg2);
                } else if (op == Op.EQUALS) {            
                        StringBuffer arg1 = translate(term.sub(0), quantifiedVars, services);
                        StringBuffer arg2 = translate(term.sub(1), quantifiedVars, services);
                        return this.translateObjectEqual(arg1, arg2);
                } else if (op == Op.ALL) {
                        ArrayOfQuantifiableVariable vars = term.varsBoundHere(0);
                        Debug.assertTrue(vars.size()==1);
                        
                        quantifiedVars.add(vars.getQuantifiableVariable(0));
                        
                        StringBuffer qv = this.translateVariable(vars.getQuantifiableVariable(0) );
                        StringBuffer sort = this.translateSort(vars.getQuantifiableVariable(0).sort());
                        StringBuffer form = this.translate(term.sub(0), quantifiedVars, services);
                        
                        if (!this.isMultiSorted()) {
                                //add the typepredicate
                                form = this.translateLogicalImply(
                                        this.getTypePredicate(vars.getQuantifiableVariable(0).sort(), qv)
                                        , form);
                        }
                        
                        quantifiedVars.remove(vars.getQuantifiableVariable(0));
                        
                        return this.translateLogicalAll(qv, sort, form);
                       
                } else if (op == Op.EX) {
                        ArrayOfQuantifiableVariable vars = term.varsBoundHere(0);
                        Debug.assertTrue(vars.size()==1);
                        
                        quantifiedVars.add(vars.getQuantifiableVariable(0));
                        
                        StringBuffer qv = this.translateVariable(vars.getQuantifiableVariable(0));
                        StringBuffer sort = this.translateSort(vars.getQuantifiableVariable(0).sort());
                        StringBuffer form = this.translate(term.sub(0), quantifiedVars, services);
                        
                        if (!this.isMultiSorted()) {
                                //add the typepredicate
                                form = this.translateLogicalImply(
                                        this.getTypePredicate(vars.getQuantifiableVariable(0).sort(), qv)
                                        , form);
                        }
                        quantifiedVars.remove(vars.getQuantifiableVariable(0));
                        
                        return this.translateLogicalExist(qv, sort, form);
                } else if (op == Op.TRUE) {
                        return this.translateLogicalTrue();
                } else if (op == Op.FALSE) {
                        return this.translateLogicalFalse();
                } else if(op == Op.NULL) {
                        //TODO translate NULL
                        return new StringBuffer("null translation to be implemented");
                } else if (op instanceof LogicVariable || op instanceof ProgramVariable) {
                        if (quantifiedVars.contains(op)) {
                                //This variable is used in the scope of a quantifier
                                //so translate it as a variable
                                return (translateVariable(op));
                        } else {
                                //this Variable is a free Variable.
                                //translate it as a constant.
                                ArrayList<StringBuffer> subterms = new ArrayList<StringBuffer>();
                                for (int i = 0; i < op.arity(); i++) {
                                        subterms.add(translate(term.sub(i), quantifiedVars, services));
                                }
                                
                                addFunction(op, new ArrayList<Sort>(), term.sort());
                                
                                return translateFunc(op, subterms);
//                                addFunction(term, getUniqueVariableName(op));
//                                return getUniqueVariableName(op);
                        }
                } else if (op instanceof Function) {
                        Function fun = (Function)op;
                        if (fun.sort() == Sort.FORMULA) {
                                //This Function is a predicate, so translate it as such
                                if (fun == services.getTypeConverter().getIntegerLDT().getLessThan() ) {        
                                        StringBuffer arg1 = translate(term.sub(0), quantifiedVars, services);
                                        StringBuffer arg2 = translate(term.sub(1), quantifiedVars, services);
                                        return this.translateIntegerLt(arg1, arg2);
                                } else if (fun == services.getTypeConverter().getIntegerLDT().getGreaterThan() ) {        
                                        StringBuffer arg1 = translate(term.sub(0), quantifiedVars, services);
                                        StringBuffer arg2 = translate(term.sub(1), quantifiedVars, services);
                                        return this.translateIntegerGt(arg1, arg2);
                                } else if (fun == services.getTypeConverter().getIntegerLDT().getLessOrEquals() ) {        
                                        StringBuffer arg1 = translate(term.sub(0), quantifiedVars, services);
                                        StringBuffer arg2 = translate(term.sub(1), quantifiedVars, services);
                                        return this.translateIntegerLeq(arg1, arg2);
                                } else if (fun == services.getTypeConverter().getIntegerLDT().getGreaterOrEquals() ) {        
                                        StringBuffer arg1 = translate(term.sub(0), quantifiedVars, services);
                                        StringBuffer arg2 = translate(term.sub(1), quantifiedVars, services);
                                        return this.translateIntegerGeq(arg1, arg2);
                                } else {
                                        ArrayList<StringBuffer> subterms = new ArrayList<StringBuffer>();
                                        for (int i = 0; i < op.arity(); i++) {
                                                subterms.add(translate(term.sub(i), quantifiedVars, services));
                                        }
                                        ArrayList<Sort> sorts = new ArrayList<Sort>();
                                        for (int i = 0; i < fun.arity(); i++) {
                                                sorts.add(fun.argSort(i));
                                        }
                                        this.addPredicate(fun, sorts);
                                        
                                        return translatePred(op, subterms);
                                }
                        } else {
                                //this Function is a function, so translate it as such
                                if (fun == services.getTypeConverter().getIntegerLDT().getAdd()) {
                                        StringBuffer arg1 = translate(term.sub(0), quantifiedVars, services);
                                        StringBuffer arg2 = translate(term.sub(1), quantifiedVars, services);
                                        return this.translateIntegerPlus(arg1, arg2);
                                } else if (fun == services.getTypeConverter().getIntegerLDT().getSub() ) { 
                                        StringBuffer arg1 = translate(term.sub(0), quantifiedVars, services);
                                        StringBuffer arg2 = translate(term.sub(1), quantifiedVars, services);
                                        return this.translateIntegerMinus(arg1, arg2);
                                } else if (fun == services.getTypeConverter().getIntegerLDT().getNeg() ) {        
                                        StringBuffer arg1 = translate(term.sub(0), quantifiedVars, services);
                                        return this.translateIntegerUnaryMinus(arg1);
                                } else if (fun == services.getTypeConverter().getIntegerLDT().getMul() ) {        
                                        StringBuffer arg1 = translate(term.sub(0), quantifiedVars, services);
                                        StringBuffer arg2 = translate(term.sub(1), quantifiedVars, services);
                                        return this.translateIntegerMult(arg1, arg2);
                                } else if (fun == services.getTypeConverter().getIntegerLDT().getDiv() ) {
                                        StringBuffer arg1 = translate(term.sub(0), quantifiedVars, services);
                                        StringBuffer arg2 = translate(term.sub(1), quantifiedVars, services);
                                        return this.translateIntegerDiv(arg1, arg2);
                                } else if (fun == services.getTypeConverter().getIntegerLDT().getNumberSymbol() ) {        
                                        Debug.assertTrue(term.arity() == 1);
                                        long num = NumberTranslation.translate(term.sub(0)).longValue();
                                        StringBuffer numVal = translateIntegerValue(num);
                                        
                                        //add the type predicate for this constant
                                        if (!this.constantTypePreds.containsKey(term)) {
                                                StringBuffer typePred = this.getTypePredicate(term.sort(), numVal);
                                                this.constantTypePreds.put(term, typePred);
                                        }
                                        
                                        return numVal;
                              } else {
                                        //an uninterpreted function. just translate it as such
                                        ArrayList<StringBuffer> subterms = new ArrayList<StringBuffer>();
                                        for (int i = 0; i < fun.arity(); i++) {
                                                subterms.add(translate(term.sub(i), quantifiedVars, services));
                                        }
                                        ArrayList<Sort> sorts = new ArrayList<Sort>();
                                        for (int i = 0; i < fun.arity(); i++) {
                                                sorts.add(fun.argSort(i));
                                        }
                                        this.addFunction(fun, sorts, fun.sort());
                                        
                                        return translateFunc(fun, subterms);
                                }
                        }
                        
                } else if (op instanceof ArrayOp) {
                        ArrayOp operation = (ArrayOp) op;
                        StringBuffer refPrefix = this.translate(operation.referencePrefix(term), quantifiedVars, services);
                        StringBuffer loc = this.translate(operation.index(term), quantifiedVars, services);
                        ArrayList<StringBuffer> subterms = new ArrayList<StringBuffer>();
                        subterms.add(refPrefix);
                        subterms.add(loc);
                        
                        ArrayList<Sort> sorts = new ArrayList<Sort>();
                        sorts.add(operation.referencePrefix(term).sort());
                        sorts.add(operation.index(term).sort());
                        
                        this.addFunction(operation, sorts, operation.sort());
                        
                        return translateFunc(operation, subterms);
                }
                //TODO AtributeAcessOp missing
                else {
                        return translateUnknown(term);
                }
        }
        
//        /**
//         * Just copies the quantified variables of term into quantifiedVars
//         * @param quantifiedVars
//         * @param term
//         */
//        protected void collectQuantifiedVars (Vector quantifiedVars, Term term) {
//                ArrayOfQuantifiableVariable vars = term.varsBoundHere(0);
//                for (int i = 0; i < vars.size(); ++i) {
//                        quantifiedVars.add(vars.getQuantifiableVariable(i));
//                }
//        }
        
//        /**
//         * Takes care of sequent tree parts that were not matched in translate(term,
//         * skolemization). In this class it just produces a warning, nothing more.
//         * It is provided as a hook for subclasses.
//         * 
//         * @param term
//         *           The Term given to translate
//         * @throws SimplifyException
//         */
//        protected StringBuffer translateUnknown(Term term) throws SimplifyException {
//                return (opNotKnownWarning(term));
//        }
        
        
        
      private StringBuffer getTypePredicate(Sort s, StringBuffer arg) {
              ArrayList<StringBuffer> arguments = new ArrayList<StringBuffer>();
              arguments.add(arg);
              StringBuffer toReturn = this.translatePredicate(typePredicates.get(s), arguments);
              
              return toReturn;
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
             //return (opNotKnownWarning(term));
             //TODO Debug message
             return new StringBuffer("unknown_Op");
     }
        
//        protected StringBuffer opNotKnownWarning(Term term)
//                        throws SimplifyException {
//                logger
//                                .warn("Warning: unknown operator while translating into Simplify "
//                                                + "syntax. Translation to Simplify will be stopped here.\n"
//                                                + "opClass="
//                                                + term.op().getClass().getName()
//                                                + ", opName="
//                                                + term.op().name()
//                                                + ", sort="
//                                                + term.sort().name());
//                throw new SimplifyException(term.op().name() + " not known by Simplify");
//        }
        
//        /**
//         * Used to give a variable (program, logic, meta) a unique name.
//         * 
//         * @param op
//         *           The variable to be translated/renamed.
//         */
/*        protected final StringBuffer translateVariable(Operator op) {
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
//                        if (!sortAxioms.contains(ax)) {
//                                sortAxioms = sortAxioms.prepend(new String[]{ax});                                                       
//                                //addPredicate(getUniqueVariableName(sort).toString(),1); 
//                        }
                }
                return res;
        }
*/
        
        protected final StringBuffer translateVariable(Operator op) {
                if (usedVariableNames.containsKey(op)) {
                        return usedVariableNames.get(op);
                } else {
                        StringBuffer var = this.translateLocicalVar(new StringBuffer(op.name().toString()));
                        usedVariableNames.put(op, var);
                        return var;
                }
        }
        
              
        /**
         * translate a function.
         * @param o the Operator used for this function.
         * @param sub The StringBuffers representing the arguments of this Function.
         * @return a StringBuffer representing the complete Function.
         */
        protected final StringBuffer translateFunc(Operator o, ArrayList<StringBuffer> sub) {
                StringBuffer name;
                if (usedFunctionNames.containsKey(o)) {
                        name = usedFunctionNames.get(o);
                } else {
                        name = translateFunctionName(new StringBuffer(o.name().toString()));
                        usedFunctionNames.put(o, name);
                }
                return translateFunction(name, sub);
        }
        
        /**
         * 
         * @param op the operator used for this function.
         * @param sorts the list of sort parameter of this function
         * @result the function's result sort
         */
        private void addFunction(Operator op, ArrayList<Sort> sorts, Sort result) {
                if (!this.functionDecls.containsKey(op)) {
                     sorts.add(result);
                     this.functionDecls.put(op, sorts);
                }
        }
        
        private void addPredicate(Operator op, ArrayList<Sort> sorts) {
                if (!this.predicateDecls.containsKey(op)) {
                        this.predicateDecls.put(op, sorts);
                   }
        }
        
        /**
         * Translate a predicate.
         * @param o the operator used for this predicate.
         * @param sub The terms representing the arguments.
         * @return a StringBuffer representing the complete predicate.
         */
        protected final StringBuffer translatePred(Operator o, ArrayList<StringBuffer> sub) {
                StringBuffer name;
                if (usedPredicateNames.containsKey(o)) {
                        name = usedPredicateNames.get(o);
                } else {
                        name = translatePredicateName(new StringBuffer(o.name().toString()));
                        usedPredicateNames.put(o, name);
                }
                return translatePredicate(name, sub);
        }
        
        protected final StringBuffer translateSort(Sort s) {
                if (usedDisplaySort.containsKey(s)) {
                        return usedDisplaySort.get(s);
                } else {
                        StringBuffer sortname = this.translateSort(s.name().toString(), isSomeIntegerSort(s));
                        StringBuffer displaysort;
                        if (this.isMultiSorted()) {
                                displaysort = sortname;
                        } else {
                                displaysort = this.getIntegerSort();
                        }
                        StringBuffer realsort = sortname;
                        
                        usedDisplaySort.put(s, displaysort);
                        usedRealSort.put(s, realsort);
                        if (!this.isMultiSorted()) {
                                addTypePredicate(realsort, s);
                        }
                        
                        return displaysort;
                }
        }
        
        /**
         * Create a type predicate for a given sort.
         * @param sortname the name, that should be used for the sort.
         * @param s the sort, this predicate belongs to.
         */
        private void addTypePredicate(StringBuffer sortname, Sort s) {
                if (!this.typePredicates.containsKey(s)) {
                        StringBuffer predName = new StringBuffer("type_of_");
                        predName.append(sortname);
                        predName = this.translatePredicateName(predName);
                        this.typePredicates.put(s, predName);
                }
        }
        
        
        
        /**
         * produces a unique name for the given Variable, starting with "KeY_" and with a
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
            return new StringBuffer("KeY_").
                append(name).
                append("_").append(getUniqueHashCode(op));
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
    protected final StringBuffer translate(Term term, int skolemization, Vector quantifiedVars, Services services)
            throws SimplifyException {
        return translate(term, quantifiedVars, services);
    }
    
    private boolean isSomeIntegerSort(Sort s) {
        if (s == jbyteSort ||
                s == jshortSort ||
                s == jintSort ||
                s == jlongSort ||
                s == jcharSort ||
                s == integerSort)
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
        
        public String getSortName(Sort s) {
                if (s.name().toString().indexOf("[") == s.name().toString().length()-2 &&
                                s.name().toString().indexOf("]") == s.name().toString().length()-1 ) {
                        //an Array is used
                        String res = s.name().toString().substring(0, s.name().toString().length() - 2);
                        res = "Array_" + res;
                        return res;
                } else if (isSomeIntegerSort(s)) {
                        return integerSort.name().toString();
                
                } else {
                        return s.name().toString();
                }
        }

}
