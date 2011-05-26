// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.speclang.jml.translation;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.speclang.translation.SLTranslationExceptionManager;
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;

import java.util.Arrays;
import java.util.Iterator;
import java.util.Map;



/**
 * Translates JML expressions to FOL.
 */
final class JMLTranslator {

    private final static JMLTranslator instance = new JMLTranslator();
    private final static TermBuilder TB = TermBuilder.DF;

    private LinkedHashMap<String, JMLTranslationMethod> translationMethods;


    private JMLTranslator() {
        translationMethods = new LinkedHashMap<String, JMLTranslationMethod>();

        // clauses
        translationMethods.put("accessible", new JMLTranslationMethod() {
            @Override
            public Term translate(Object... params)
                    throws SLTranslationException {
                checkParameters(params, Term.class, Services.class);
                Term ensuresTerm = (Term) params[0];
                Services services = (Services) params[1];
                return TB.convertToFormula(ensuresTerm, services);
            }
        });
        translationMethods.put("assignable", new JMLTranslationMethod() {
            @Override
            public Term translate(Object... params)
                    throws SLTranslationException {
                checkParameters(params, Term.class, Services.class);
                Term ensuresTerm = (Term) params[0];
                Services services = (Services) params[1];
                return TB.convertToFormula(ensuresTerm, services);
            }
        });
        translationMethods.put("depends", new JMLTranslationMethod() {
            @Override
            public Triple translate(Object... params)
                    throws SLTranslationException {
                checkParameters(params, SLExpression.class, Term.class,
                                SLExpression.class,
                                SLTranslationExceptionManager.class,
                                Services.class);
                SLExpression lhs = (SLExpression) params[0];
                Term rhs = (Term) params[1];
                SLExpression mby = (SLExpression) params[2];
                SLTranslationExceptionManager excManager =
                        (SLTranslationExceptionManager) params[3];
                Services services = (Services) params[4];

                LocationVariable heap =
                        services.getTypeConverter().getHeapLDT().getHeap();
                if (!lhs.isTerm()
                    || !(lhs.getTerm().op() instanceof ObserverFunction)
                    || lhs.getTerm().sub(0).op() != heap) {
                    excManager.createException("Depends clause with unexpected lhs: " + lhs);
                }
                return new Triple<ObserverFunction, Term, Term>(
                        (ObserverFunction) lhs.getTerm().op(),
                        rhs,
                        mby == null ? null : mby.getTerm());
            }
        });
        translationMethods.put("ensures", new JMLTranslationMethod() {
            @Override
            public Term translate(Object... params)
                    throws SLTranslationException {
                checkParameters(params, Term.class, Services.class);
                Term ensuresTerm = (Term) params[0];
                Services services = (Services) params[1];
                return TB.convertToFormula(ensuresTerm, services);
            }
        });
        translationMethods.put("represents", new JMLTranslationMethod() {
            @Override
            public Pair translate(Object... params)
                    throws SLTranslationException {
                checkParameters(params, SLExpression.class, Term.class,
                        Services.class);
                SLExpression lhs = (SLExpression) params[0];
                Term t = (Term) params[1];

                return new Pair<ObserverFunction,Term>(
                     (ObserverFunction) lhs.getTerm().op(),
                     t);
            }
        });
        translationMethods.put("signals", new JMLTranslationMethod() {
            @Override
            public Term translate(Object... params)
                    throws SLTranslationException {
                checkParameters(params, Term.class, LogicVariable.class,
                        ProgramVariable.class, KeYJavaType.class,
                        Services.class);
                Term result = (Term) params[0];
                LogicVariable eVar = (LogicVariable) params[1];
                ProgramVariable excVar = (ProgramVariable) params[2];
                KeYJavaType excType = (KeYJavaType) params[3];
                Services services = (Services) params[4];

                if (result == null) {
                    result = TB.tt();
                } else {
                    Map /* Operator -> Operator */ replaceMap =
                            new LinkedHashMap();
                    replaceMap.put(eVar, excVar);
                    OpReplacer excVarReplacer = new OpReplacer(replaceMap);

                    Sort os = excType.getSort();
                    Function instance = os.getInstanceofSymbol(services);

                    result = TB.imp(
                            TB.equals(TB.func(instance, TB.var(excVar)), TB.TRUE(
                            services)),
                            TB.convertToFormula(excVarReplacer.replace(result),
                                                services));
                }
                return result;
            }
        });
        translationMethods.put("signals_only", new JMLTranslationMethod() {
            @Override
            public Term translate(Object... params)
                    throws SLTranslationException {
                checkParameters(params,
                                ImmutableList.class, ProgramVariable.class,
                                Services.class);
                ImmutableList<KeYJavaType> signalsonly =
                        (ImmutableList<KeYJavaType>) params[0];
                ProgramVariable excVar = (ProgramVariable) params[1];
                Services services = (Services) params[2];
                // Build appropriate term out of the parsed list of types
                // i.e. disjunction of "excVar instanceof ExcType"
                // for every ExcType in the list
                Term result = TB.ff();

                Iterator<KeYJavaType> it = signalsonly.iterator();
                while (it.hasNext()) {
                    KeYJavaType kjt = it.next();
                    Function instance = kjt.getSort().getInstanceofSymbol(
                            services);
                    result = TB.or(result,
                                   TB.equals(
                            TB.func(instance, TB.var(excVar)),
                            TB.TRUE(services)));
                }

                return result;
            }
        });

        // quantifiers
        translationMethods.put("\\forall", new JMLQuantifierTranslationMethod() {
            @Override
            public Term translateQuantifier(QuantifiableVariable qv,
                                            Term t)
                    throws SLTranslationException {
                return TB.all(qv, t);
            }
            @Override
            public Term combineQuantifiedTerms(Term t1,
                                               Term t2)
                    throws SLTranslationException {
                return TB.imp(t1, t2);
            }
        });
        translationMethods.put("\\exists", new JMLQuantifierTranslationMethod() {
            @Override
            public Term translateQuantifier(QuantifiableVariable qv,
                                            Term t)
                    throws SLTranslationException {
                return TB.ex(qv, t);
            }
            @Override
            public Term combineQuantifiedTerms(Term t1,
                                               Term t2)
                    throws SLTranslationException {
                return TB.and(t1, t2);
            }
        });
        translationMethods.put("\\bsum", new JMLTranslationMethod() {
            @Override
            public SLExpression translate(Object... params)
                    throws SLTranslationException {
                checkParameters(params,
                                SLExpression.class, SLExpression.class,
                                SLExpression.class, KeYJavaType.class,
                                ImmutableList.class, Services.class);
                SLExpression a = (SLExpression) params[0];
                SLExpression b = (SLExpression) params[1];
                SLExpression t = (SLExpression) params[2];
                KeYJavaType declsType = (KeYJavaType) params[3];
                ImmutableList<LogicVariable> declVars =
                        (ImmutableList<LogicVariable>) params[4];
                Services services = (Services)params[5];

                if (!declsType.getJavaType().equals(PrimitiveType.JAVA_INT)) {
                    throw new SLTranslationException("bounded sum variable must be of type int");
                } else if (declVars.size() != 1) {
                    throw new SLTranslationException("bounded sum must declare exactly one variable");
                }
                LogicVariable qv = (LogicVariable) declVars.head();
                Term resultTerm = TB.bsum(qv, a.getTerm(), b.getTerm(), t.getTerm(), services);
                return new SLExpression(resultTerm, t.getType());
            }
        });
//        translationMethods.put("\\min", new Name("min"));
//        translationMethods.put("\\max", new Name("max"));
//        translationMethods.put("\\num_of", new Name("num_of"));
//        translationMethods.put("\\product", new Name("product"));
        translationMethods.put("\\sum", new JMLBoundedNumericalQuantifierTranslationMethod(){
                @Override
                public Term emptyRangeValue() {
                        return TB.zero(services);
                }
                @Override
                public Term translateBoundedNumericalQuantifier(
                                QuantifiableVariable qv, Term lo, Term hi,
                                Term body) {
                        return TB.bsum(qv, lo, hi, body, services);               } 
        }
        );
        
        // primary expressions
        translationMethods.put("\\not_modified", new JMLPostExpressionTranslationMethod(){

            @Override
            protected String name() {
                return "\\not_modified";
            }

            @Override
            protected Term translate(Services services, Term heapAtPre, Object[] params) throws SLTranslationException {
                checkParameters(params, Term.class);
                Term t = (Term) params[0];
                
                // collect variables from storereflist
                java.util.List<Term> storeRefs = new java.util.ArrayList<Term>();
                final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
                final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
                while (t.op() == ldt.getUnion()){
                    storeRefs.add(t.sub(0));
                    t = t.sub(1);
                }
                storeRefs.add(t);
                // construct equality predicates
                Term res = TB.tt();
                for (Term sr: storeRefs){
                    if (sr.op() == ldt.getSingleton()){
                        final Term ref = TB.dot(services, Sort.ANY, sr.sub(0), sr.sub(1));
                        res = TB.and(res, TB.equals(ref,convertToOld(services, heapAtPre, ref)));
                    } else if (sr.op() == ldt.getEmpty()){
                        // do nothing
                    } else if (sr.op().equals(ldt.getSetMinus()) && sr.sub(0).op().equals(ldt.getAllLocs()) && sr.sub(1).op().equals(ldt.getFreshLocs())){
                        // this is the case for "\everything"
                        final JavaInfo ji = services.getJavaInfo();
                        final LogicVariable fld = new LogicVariable(new Name("f"), heapLDT.getFieldSort());
                        final LogicVariable obj = new LogicVariable(new Name("o"), ji.objectSort());
                        final Term objTerm = TB.var(obj);
                        final Term fldTerm = TB.var(fld);
                        final Term ref = TB.dot(services, Sort.ANY, objTerm, fldTerm);
                        final Term fresh = TB.subset(services, TB.singleton(services, objTerm, fldTerm ), TB.freshLocs(services, heapAtPre));
                        final Term bodyTerm = TB.or(TB.equals(ref, convertToOld(services, heapAtPre, ref)),fresh);
                        res = TB.and(res, TB.all(fld, TB.all(obj, bodyTerm)));
                    } else {
                        // all other results are not meant to occur
                        throw new SLTranslationException("Term "+sr+" is not a valid store-ref expression.");
                    }
                }
                return res;
            }

        });

        // operators
        translationMethods.put("<==>", new JMLEqualityTranslationMethod() {
            @Override
            public SLExpression translate(Object... params)
                    throws SLTranslationException {
                checkParameters(params,
                                SLExpression.class, SLExpression.class,
                                SLTranslationExceptionManager.class,
                                Services.class);
                SLExpression expr1 = (SLExpression) params[0];
                SLExpression expr2 = (SLExpression) params[1];
                SLTranslationExceptionManager excManager =
                        (SLTranslationExceptionManager) params[2];
                Services services = (Services) params[3];

                checkSLExpressions(expr1, expr2, excManager, "<==>");
                return buildEqualityTerm(expr1, expr2, excManager, services);
            }
        });
        translationMethods.put("<=!=>", new JMLEqualityTranslationMethod() {
            @Override
            public SLExpression translate(Object... params)
                    throws SLTranslationException {
                checkParameters(params,
                                SLExpression.class, SLExpression.class,
                                SLTranslationExceptionManager.class,
                                Services.class);
                SLExpression expr1 = (SLExpression) params[0];
                SLExpression expr2 = (SLExpression) params[1];
                SLTranslationExceptionManager excManager =
                        (SLTranslationExceptionManager) params[2];
                Services services = (Services) params[3];

                checkSLExpressions(expr1, expr2, excManager, "<=!=>");
                SLExpression eq =
                        buildEqualityTerm(expr1, expr2, excManager, services);
                return new SLExpression(TB.not(eq.getTerm()), eq.getType());
            }
        });
        translationMethods.put("==", new JMLEqualityTranslationMethod() {
            @Override
            public SLExpression translate(Object... params)
                    throws SLTranslationException {
                checkParameters(params,
                                SLExpression.class, SLExpression.class,
                                SLTranslationExceptionManager.class,
                                Services.class);
                SLExpression expr1 = (SLExpression) params[0];
                SLExpression expr2 = (SLExpression) params[1];
                SLTranslationExceptionManager excManager =
                        (SLTranslationExceptionManager) params[2];
                Services services = (Services) params[3];

                checkSLExpressions(expr1, expr2, excManager, "==");
                return buildEqualityTerm(expr1, expr2, excManager, services);
            }
        });
        translationMethods.put("!=", new JMLEqualityTranslationMethod() {
            @Override
            public SLExpression translate(Object... params)
                    throws SLTranslationException {
                checkParameters(params,
                                SLExpression.class, SLExpression.class,
                                SLTranslationExceptionManager.class,
                                Services.class);
                SLExpression expr1 = (SLExpression) params[0];
                SLExpression expr2 = (SLExpression) params[1];
                SLTranslationExceptionManager excManager =
                        (SLTranslationExceptionManager) params[2];
                Services services = (Services) params[3];

                checkSLExpressions(expr1, expr2, excManager, "!=");
                SLExpression eq =
                        buildEqualityTerm(expr1, expr2, excManager, services);
                if (eq.getType() != null) {
                    return new SLExpression(TB.not(eq.getTerm()), eq.getType());
                } else {
                    return new SLExpression(TB.not(eq.getTerm()));
                }
            }
        });
    }



    //-------------------------------------------------------------------------
    // public methods
    //-------------------------------------------------------------------------


    public static JMLTranslator getInstance() {
        return instance;
    }


    public <T> T translate(String jmlKeyword,
                          Object... params)
            throws SLTranslationException {
        JMLTranslationMethod m = translationMethods.get(jmlKeyword);
        if (m != null) {
            Object result = m.translate(params);
            this.<T>checkReturnType(result);
            return (T) result;
        } else {
            throw new SLTranslationException(
                    "Unknown translation for JML-keyword \""
                    + jmlKeyword
                    + "\". The keyword seems not to be supported yet.");
        }
    }


    /**
     *
     */
    public <T> T parse(PositionedString expr,
                       KeYJavaType specInClass,
                       ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       ProgramVariable resultVar,
                       ProgramVariable excVar,
                       Term heapAtPre,
                       Services services)
            throws SLTranslationException {
        final KeYJMLParser parser = new KeYJMLParser(expr, services,
                                                     specInClass, selfVar,
                                                     paramVars, resultVar,
                                                     excVar, heapAtPre);
        Object result = null;
	try {
	    result = parser.top();
	} catch (antlr.ANTLRException e) {
	    throw parser.getExceptionManager().convertException(e);
	}
        this.<T>checkReturnType(result);
        return (T) result;
    }


    //-------------------------------------------------------------------------
    // private methods
    //-------------------------------------------------------------------------


    private void checkParameters(Object[] params,
                                 Class... classes)
            throws SLTranslationException {
        boolean ok = true;
        int i = 0;
        while (i < params.length && i < classes.length && ok) {
            ok &= params[i] == null || classes[i].isInstance(params[i]);
            i++;
        }
        if (!ok) {
            throw new SLTranslationException(
                    "Parameter " + i + " does not match the expected type.\n"
                     + "Parameter type was: " + params[i - 1].getClass().getName()
                     + "\nExpected type was:  " + classes[i - 1].getName());
        } else if (i < classes.length) {
            throw new SLTranslationException(
                    "Parameter" + i + " is missing. The expected type is \""
                    + classes[i].toString() + "\".");
        } else if (i < params.length) {
            throw new SLTranslationException(
                    (params.length - i) + " more parameters than expected.");
        }
    }


    private <T> void checkReturnType(Object result)
            throws SLTranslationException {
        try {
            result = (T) result;
        } catch (ClassCastException e) {
            throw new SLTranslationException(
                    "Return value does not match the expected return type:\n"
                    + "Return type was: " + result.getClass() + "\n"
                    + "Tried conversion was: " + e.getMessage());
        }
    }


    //-------------------------------------------------------------------------
    // private classes
    //-------------------------------------------------------------------------

    
    private abstract class JMLQuantifierTranslationMethod implements
            JMLTranslationMethod {
            
            protected Services services;


        /**
         * Add implicit "non-null" and "created" guards for reference types,
         * "in-bounds" guards for integer types. Then, translateToTerm the quantifier.
         * @param quantName
         * @param declVars
         * @param expr
         * @param preTerm
         * @param bodyTerm
         * @param nullable
         * @param services
         * @return
         * @throws SLTranslationException
         */
        @SuppressWarnings("unchecked")
        @Override
        public Term translate(Object... params)
                throws SLTranslationException {
            checkParameters(params,
                            Term.class, Term.class, KeYJavaType.class,
                            ImmutableList.class, Boolean.class, Services.class);
            Term preTerm = (Term) params[0];
            Term bodyTerm = (Term) params[1];
            KeYJavaType declsType = (KeYJavaType) params[2];
            ImmutableList<LogicVariable> declVars =
                    (ImmutableList<LogicVariable>) params[3];
            boolean nullable = (Boolean) params[4];
            services = (Services) params[5];

            Term nullTerm = TB.NULL(services);
            for (LogicVariable lv : declVars) {
                preTerm = TB.and(preTerm,
                                 TB.reachableValue(services, TB.var(lv),
                                                   declsType));
                if (lv.sort().extendsTrans(services.getJavaInfo().objectSort())
                    && !nullable) {
                    preTerm = TB.and(preTerm, TB.not(TB.equals(TB.var(lv),
                                                               nullTerm)));
                }
            }

            return translateQuantifiers(declVars, preTerm, bodyTerm);
        }


        public Term translateQuantifiers(Iterable<LogicVariable> qvs,
                                         Term t1,
                                         Term t2)
                throws SLTranslationException {
            Term result = combineQuantifiedTerms(t1, t2);
            for (LogicVariable qv : qvs) {
                result = translateQuantifier(qv, result);
            }
            return result;
        }

        public abstract Term combineQuantifiedTerms(Term t1,
                                                    Term t2)
                throws SLTranslationException;

        public abstract Term translateQuantifier(QuantifiableVariable qv,
                                                 Term t)
                throws SLTranslationException;
    }

    private abstract class JMLBoundedNumericalQuantifierTranslationMethod extends JMLQuantifierTranslationMethod {
            final static String notBounded = "Only numerical quantifier expressions of form (\\sum int i; l<=i && i<u; t) are permitted";
            final static String notInt = "Bounded numerical quantifier variable must be of type int.";


            private  boolean isBoundedNumerical(Term a, LogicVariable lv){
                    return lowerBound(a,lv)!=null && upperBound(a,lv)!=null;
            }

            /**
             * Extracts lower bound from <code>a</code> if it matches the pattern.
             * @param a guard to be disected
             * @param lv variable bound by quantifier
             * @return lower bound term (or null)
             */
            private  Term lowerBound(Term a, LogicVariable lv){
                    if(a.arity()>0 && a.sub(0).op()==Junctor.AND){
                            a=a.sub(0);
                    }
                    if(a.arity()==2 && a.op()== Junctor.AND && a.sub(0).arity()==2 && a.sub(0).sub(1).op()==lv
                                    && a.sub(0).op().equals(services.getTypeConverter().getIntegerLDT().getLessOrEquals())){
                            return a.sub(0).sub(0);
                    }
                    return null;
            }

            /**
             * Extracts upper bound from <code>a</code> if it matches the pattern.
             * @param a guard to be disected
             * @param lv variable bound by quantifier
             * @return upper bound term (or null)
             */
            private Term upperBound(Term a, LogicVariable lv){
                    if(a.arity()>0 && a.sub(0).op()==Junctor.AND){
                            a=a.sub(0);
                    }   
                    if(a.arity()==2 && a.op()==Junctor.AND && a.sub(1).arity()==2 && a.sub(1).sub(0).op()==lv
                                    && a.sub(1).op().equals(services.getTypeConverter().getIntegerLDT().getLessThan())){
                            return a.sub(1).sub(1);
                    }
                    return null;
            }


            @Override
            public Term translate(Object... params)
            throws SLTranslationException {
                    checkParameters(params,
                                    Term.class, Term.class, KeYJavaType.class,
                                    ImmutableList.class, Boolean.class, Services.class);
                    KeYJavaType declsType = (KeYJavaType) params[2];
                    if (!declsType.getJavaType().equals(PrimitiveType.JAVA_INT))
                            throw new SLTranslationException(notInt);
                    return super.translate(params);
            }

            @Override
            public Term translateQuantifiers(Iterable<LogicVariable> qvs, Term t1, Term t2)
            throws SLTranslationException {
                    Iterator<LogicVariable> it = qvs.iterator();
                    LogicVariable lv = it.next();
                    if (it.hasNext() || !isBoundedNumerical(t1, lv)){
                            throw new SLTranslationException(notBounded);
                    } else {
                            if (t1.arity()>0 && t1.sub(0).op()==Junctor.AND)
                                    t2 = TB.ife(t1.sub(1), t2, emptyRangeValue());
                            return translateBoundedNumericalQuantifier(lv, lowerBound(t1, lv), upperBound(t1, lv), t2);
                    }
            }

            /** Creates a term for a bounded numerical quantifier (e.g., sum).*/
            public abstract Term translateBoundedNumericalQuantifier(QuantifiableVariable qv, Term lo, Term hi, Term body);

            /** Gives the defined term for an empty range to quantify over (e.g., zero for sum). */
            public abstract Term emptyRangeValue ();

            /** Should not be called. */
            @Override
            @Deprecated
            public Term combineQuantifiedTerms(Term t1, Term t2){
                    assert false;
                    return null;
            }
            /** Should not be called. */
            @Override
            @Deprecated
            public Term translateQuantifier(QuantifiableVariable qv,
                            Term t){
                    assert false;
                    return null;
            }
    }
    
    /**
     * Translation method for expressions only allowed to appear in a postcondition.
     * @author bruns
     *
     */
    private abstract class JMLPostExpressionTranslationMethod implements JMLTranslationMethod {

        protected void assertPost (Term heapAtPre) throws SLTranslationException{
            if (heapAtPre == null){
                throw new SLTranslationException("JML construct "+name()+" not allowed in this context.");
            }
        }
        

        /**
         * Converts a term so that all of its non-rigid operators refer to the pre-state.
         */
        protected Term convertToOld(Services services, Term heapAtPre, Term term) {
            assert heapAtPre != null;
            Map<Term,Term> map = new LinkedHashMap<Term, Term>();
            map.put(TB.heap(services), heapAtPre);
            OpReplacer or = new OpReplacer(map);
            return or.replace(term);
        }

        /**
         * Name of this translation method;
         */
        protected abstract String name();

        protected abstract Term translate (Services services, Term heapAtPre, Object[] params) throws SLTranslationException;

        public Term translate (Object ... params) throws SLTranslationException{
            if (!(params[0] instanceof Services && params[1] instanceof Term))
                throw new SLTranslationException(
                        "Parameter 2 does not match the expected type.\n"
                        + "Parameter type was: " + params[1].getClass().getName()
                        + "\nExpected type was:  Term");
            Term heapAtPre = (Term) params[1];
            assertPost(heapAtPre);
            return translate((Services)params[0], heapAtPre, Arrays.copyOfRange(params, 1, params.length-1));
        }
    }


    private abstract class JMLEqualityTranslationMethod implements
            JMLTranslationMethod {

        protected void checkSLExpressions(SLExpression expr1,
                                          SLExpression expr2,
                                          SLTranslationExceptionManager excManager,
                                          String eqSymb) {
            if (expr1.isType() != expr2.isType()) {
                excManager.createException(
                        "Cannot build equality expression (" + eqSymb
                        + ") between term and type.");
            }

        }


        protected SLExpression buildEqualityTerm(SLExpression a,
                                                 SLExpression b,
                                                 SLTranslationExceptionManager excManager,
                                                 Services services)
                throws SLTranslationException {

            if (a.isTerm() && b.isTerm()) {
                return new SLExpression(buildEqualityTerm(a.getTerm(),
                                                          b.getTerm(),
                                                          excManager,
                                                          services));
            }

            if (a.isType() && b.isType()) {
                SLExpression typeofExpr;
                SLExpression typeExpr;
                if (a.getTerm() != null) {
                    typeofExpr = a;
                    typeExpr = b;
                } else {
                    if (b.getTerm() == null) {
                        excManager.createException(
                                "Type equality only supported for expressions "
                                + " of shape \"\\typeof(term) == \\type(Typename)\"");
                    }
                    typeofExpr = b;
                    typeExpr = a;
                }

                Sort os = typeExpr.getType().getSort();
                Function ioFunc = os.getExactInstanceofSymbol(services);

                return new SLExpression(TB.equals(
                        TB.func(ioFunc, typeofExpr.getTerm()),
                        TB.TRUE(services)));
            }

            return null;
        }


        protected Term buildEqualityTerm(Term a,
                                         Term b,
                                         SLTranslationExceptionManager excManager,
                                         Services services)
                throws SLTranslationException {

            Term result = null;
            try {
                if (a.sort() != Sort.FORMULA && b.sort() != Sort.FORMULA) {
                    result = TB.equals(a, b);
                } else {
                    result = TB.equals(TB.convertToFormula(a, services),
                                       TB.convertToFormula(b, services));
                }
            } catch (IllegalArgumentException e) {
                excManager.createException(
                        "Illegal Arguments in equality expression.");
                //"near " + LT(0));
            } catch (TermCreationException e) {
                excManager.createException("Error in equality-expression\n"
                                           + a.toString() + " == "
                                           + b.toString() + ".");
            }

            return result;
        }
    }
}
