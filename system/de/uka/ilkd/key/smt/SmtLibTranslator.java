package de.uka.ilkd.key.smt;

import java.util.ArrayList;
import java.util.HashMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.SetOfMetavariable;
import de.uka.ilkd.key.proof.decproc.ConstraintSet;
import de.uka.ilkd.key.proof.decproc.SimplifyException;

public class SmtLibTranslator extends AbstractSmtTranslator {

        //counter used for making names unique
        private int counter = 0;
        
        private static StringBuffer INTSTRING = new StringBuffer("int");
        
        private static StringBuffer FALSESTRING = new StringBuffer("false");
        private static StringBuffer TRUESTRING = new StringBuffer("true");
        private static StringBuffer ALLSTRING = new StringBuffer("forall");
        private static StringBuffer EXISTSTRING = new StringBuffer("exists");
        private static StringBuffer ANDSTRING = new StringBuffer("and");
        private static StringBuffer ORSTRING = new StringBuffer("or");
        private static StringBuffer NOTSTRING = new StringBuffer("not");
        private static StringBuffer EQSTRING = new StringBuffer("=");
        private static StringBuffer IMPLYSTRING = new StringBuffer("implies");
        private static StringBuffer PLUSSTRING = new StringBuffer("+");
        private static StringBuffer MINUSSTRING = new StringBuffer("-");
        private static StringBuffer MULTSTRING = new StringBuffer("*");
        private static StringBuffer LTSTRING = new StringBuffer("<");
        private static StringBuffer GTSTRING = new StringBuffer(">");
        private static StringBuffer LEQSTRING = new StringBuffer("<=");
        private static StringBuffer GEQSTRING = new StringBuffer(">=");
        
        
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
        public SmtLibTranslator(Sequent sequent, ConstraintSet cs,
                                   SetOfMetavariable localmv, 
                                   Services services,
                                   boolean lightWeight) 
            throws SimplifyException {
                super(sequent, cs,
                                localmv, 
                                services,
                                lightWeight);
        }

        public SmtLibTranslator(Sequent sequent, ConstraintSet cs,
                                   SetOfMetavariable localmv, 
                                   Services services) 
                throws SimplifyException {
                super(sequent, cs,
                                localmv, 
                                services);
        }

        /**
         * For translating only terms and not complete sequents.
         */
        public SmtLibTranslator(Services s) throws SimplifyException{
                super(s);
        }
        
        
        @Override
        public StringBuffer buildCompleteText(StringBuffer formula
                        , ArrayList<ArrayList<StringBuffer>> functions
                        , ArrayList<ArrayList<StringBuffer>> predicates
                        , ArrayList<StringBuffer> types) {
               StringBuffer toReturn = new StringBuffer("( benchmark KeY-translation\n");
               //add the sortdeclarations
               //as sortshirarchies are not supported by smt-lib, only one sort should be used
               //no extra sorts needed
               
               
               //add the sort declarations
               toReturn.append("\n :extrasorts (");
               for (StringBuffer s : types) {
                       if (!(s == INTSTRING || s.equals(INTSTRING))) {
                               toReturn.append(s);
                               toReturn.append(" ");
                       }
               }
               toReturn.append(")");
               
               //add the predicate declarations
               toReturn.append("\n:extrapreds (");
               for (ArrayList<StringBuffer> a : predicates) {
                       toReturn.append("(");
                       for (StringBuffer s : a) {
                               toReturn.append(s);  
                               toReturn.append(" "); 
                       }
                       toReturn.append(") ");
               }
               toReturn.append(")");
               
               //add the function declarations
               toReturn.append("\n:extrafuns (");
               for (ArrayList<StringBuffer> a : functions) {
                       toReturn.append("(");
                       for (StringBuffer s : a) {
                               toReturn.append(s);  
                               toReturn.append(" "); 
                       }
                       toReturn.append(") ");
               }
               toReturn.append(")");
               
               //add the formula
               toReturn.append("\n:formula ").append(formula).append("\n");
               
               toReturn.append(")");
               
               return toReturn;
                
        }

        /**
         * Translate a sort.
         * 
         * @param name the sorts name
         * @param isIntVal true, if the sort should represent some kind of integer
         * 
         * @return Argument 1 of the return value is the sort used in var declarations,
         *      Argument2 is the sort used for type predicates
         */
        public StringBuffer translateSort(String name, boolean isIntVal) {
               // ArrayList<StringBuffer> toReturn = new ArrayList<StringBuffer>();
                StringBuffer uniqueName = makeUnique(new StringBuffer(name));
                //if (isIntVal) {
                //        toReturn.add(INTSTRING);
                //} else {
                //        toReturn.add(uniqueName);
                //}
                //toReturn.add(uniqueName);
                return uniqueName;
        }

        @Override
        public boolean isMultiSorted() {
                return false;
        }
        
        @Override
        public StringBuffer getIntegerSort() {
                return INTSTRING;
        }
        
        @Override
        public StringBuffer translateFunction(StringBuffer name,
                        ArrayList<StringBuffer> args) {
                return buildFunction(name, args);
        }

        @Override
        public StringBuffer translateFunctionName(StringBuffer name) {
                return makeUnique(name);
        }

        @Override
        public StringBuffer translateIntegerDiv(StringBuffer arg1,
                        StringBuffer arg2) {
//                ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
//                args.add(arg1);
//                args.add(arg2);
                return new StringBuffer("unknownOp");
        }

        @Override
        public StringBuffer translateIntegerGeq(StringBuffer arg1,
                        StringBuffer arg2) {
                ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
                args.add(arg1);
                args.add(arg2);
                return buildFunction(GEQSTRING, args);
        }

        @Override
        public StringBuffer translateIntegerGt(StringBuffer arg1,
                        StringBuffer arg2) {
                ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
                args.add(arg1);
                args.add(arg2);
                return buildFunction(GTSTRING, args);
        }

        @Override
        public StringBuffer translateIntegerLeq(StringBuffer arg1,
                        StringBuffer arg2) {
                ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
                args.add(arg1);
                args.add(arg2);
                return buildFunction(LEQSTRING, args);
        }

        @Override
        public StringBuffer translateIntegerLt(StringBuffer arg1,
                        StringBuffer arg2) {
                ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
                args.add(arg1);
                args.add(arg2);
                return buildFunction(LTSTRING, args);
        }

        @Override
        public StringBuffer translateIntegerMinus(StringBuffer arg1,
                        StringBuffer arg2) {
                ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
                args.add(arg1);
                args.add(arg2);
                return buildFunction(MINUSSTRING, args);
        }

        @Override
        public StringBuffer translateIntegerMod(StringBuffer arg1,
                        StringBuffer arg2) {
                return new StringBuffer("unknownOp");
        }

        @Override
        public StringBuffer translateIntegerMult(StringBuffer arg1,
                        StringBuffer arg2) {
                ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
                args.add(arg1);
                args.add(arg2);
                return buildFunction(MULTSTRING, args);
        }

        @Override
        public StringBuffer translateIntegerPlus(StringBuffer arg1,
                        StringBuffer arg2) {
                ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
                args.add(arg1);
                args.add(arg2);
                return buildFunction(PLUSSTRING, args);
        }

        @Override
        public StringBuffer translateIntegerUnaryMinus(StringBuffer arg) {
                ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
                StringBuffer n = new StringBuffer("0");
                args.add(n);
                args.add(arg);
                return buildFunction(MINUSSTRING, args);
        }

        @Override
        public StringBuffer translateIntegerValue(long val) {
                StringBuffer arg;
                if (val < 0) {
                        arg = translateIntegerValue(val * (-1));
                        arg = translateIntegerUnaryMinus(arg);
                } else {
                        arg = new StringBuffer(Long.toString(val));
                }
                
                return arg;
        }

        @Override
        public StringBuffer translateLocicalConstant(StringBuffer name) {
                return makeUnique(name);
        }

        @Override
        public StringBuffer translateLocicalVar(StringBuffer name) {
                StringBuffer toReturn = (new StringBuffer("?")).append(makeUnique(name));
                return toReturn;
        }

        @Override
        public StringBuffer translateLogicalAll(StringBuffer var,
                        StringBuffer type, StringBuffer form) {
                StringBuffer toReturn = new StringBuffer();
                toReturn.append("(");
                toReturn.append(ALLSTRING);
                
                toReturn.append(" (");
                toReturn.append(var);
                toReturn.append(" ");
                toReturn.append(type);
                toReturn.append(") ");
                
                toReturn.append(form);
                
                toReturn.append(")");
                return toReturn;
        }

        @Override
        public StringBuffer translateLogicalAnd(StringBuffer arg1,
                        StringBuffer arg2) {
                ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
                args.add(arg1);
                args.add(arg2);
                return buildFunction(ANDSTRING, args);
        }

        @Override
        public StringBuffer translateLogicalEquivalence(StringBuffer arg1,
                        StringBuffer arg2) {
                ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
                args.add(arg1);
                args.add(arg2);
                
                ArrayList<StringBuffer> argsrev = new ArrayList<StringBuffer>();
                argsrev.add(arg2);
                argsrev.add(arg1);
                
                ArrayList<StringBuffer> forms = new ArrayList<StringBuffer>();
                forms.add(buildFunction(IMPLYSTRING, args));
                forms.add(buildFunction(IMPLYSTRING, argsrev));
                return buildFunction(ANDSTRING, forms);
        }

        @Override
        public StringBuffer translateLogicalExist(StringBuffer var,
                        StringBuffer type, StringBuffer form) {
                StringBuffer toReturn = new StringBuffer();
                toReturn.append("(");
                toReturn.append(EXISTSTRING);
                
                toReturn.append("(");
                toReturn.append(var);
                toReturn.append(" ");
                toReturn.append(type);
                toReturn.append(")");
                
                toReturn.append(form);
                
                toReturn.append(")");
                return toReturn;
        }

        @Override
        public StringBuffer translateLogicalFalse() {
                return new StringBuffer(FALSESTRING);
        }

        @Override
        public StringBuffer translateLogicalImply(StringBuffer arg1,
                        StringBuffer arg2) {
                ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
                args.add(arg1);
                args.add(arg2);
                return buildFunction(IMPLYSTRING, args);
        }

        @Override
        public StringBuffer translateLogicalNot(StringBuffer arg) {
                ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
                args.add(arg);
                return buildFunction(NOTSTRING, args);
        }

        @Override
        public StringBuffer translateLogicalOr(StringBuffer arg1,
                        StringBuffer arg2) {
                ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
                args.add(arg1);
                args.add(arg2);
                return buildFunction(ORSTRING, args);
        }

        @Override
        public StringBuffer translateLogicalTrue() {
                return new StringBuffer(TRUESTRING);
        }

        @Override
        public StringBuffer translateObjectEqual(StringBuffer arg1,
                        StringBuffer arg2) {
                ArrayList<StringBuffer> args = new ArrayList<StringBuffer>();
                args.add(arg1);
                args.add(arg2);
                return buildFunction(EQSTRING, args);
        }

        @Override
        public StringBuffer translatePredicate(StringBuffer name,
                        ArrayList<StringBuffer> args) {
                return buildFunction(name, args);
        }

        @Override
        public StringBuffer translatePredicateName(StringBuffer name) {
                return makeUnique(name);
        }

        
        private StringBuffer buildFunction(StringBuffer name, ArrayList<StringBuffer> args) {
                StringBuffer toReturn = new StringBuffer();
                if (args.size() == 0) {
                        toReturn.append(name);
                } else {
                        toReturn.append("(");
                        toReturn.append(name);
                        for (int i = 0; i < args.size(); i++) {
                                toReturn.append(" ");
                                toReturn.append(args.get(i));
                        }
                        toReturn.append(")");
                }
                return toReturn;
        }
        
        //TODO remove illegal chars
        private StringBuffer makeUnique(StringBuffer name) {
                StringBuffer toReturn = new StringBuffer(name);
                toReturn.append("_").append(counter);
                counter++;
                return toReturn;
        }

}
