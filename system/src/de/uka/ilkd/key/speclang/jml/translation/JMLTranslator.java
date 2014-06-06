// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang.jml.translation;

import java.util.ArrayList;
import java.util.EnumMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import antlr.Token;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.JMLSpecExtractor;
import de.uka.ilkd.key.speclang.translation.JavaIntegerSemanticsHelper;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.speclang.translation.SLTranslationExceptionManager;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;



/**
 * Translates JML expressions to FOL.
 */
final class JMLTranslator {

    private final TermBuilder tb; 
    private final String fileName;
    private TermServices services;                          // to be used in future
    private SLTranslationExceptionManager excManager;
    private List<PositionedString> warnings = new ArrayList<PositionedString>();

    private EnumMap<JMLKeyWord, JMLTranslationMethod> translationMethods;

    public static enum JMLKeyWord {
    	// general features, not necessarily keywords
        ARRAY_REF ("array reference"),
        INV ("\\inv"),
        INV_FOR ("\\invariant_for"),
        CAST ("cast"),
        CONDITIONAL ("conditional"),
        FRESH ("\\fresh"),

        // clauses
        ACCESSIBLE ("accessible"),
        ASSIGNABLE ("assignable"),
        DEPENDS ("depends"),
        ENSURES ("ensures"),
        MODEL_METHOD_AXIOM ("model_method_axiom"),
        REPRESENTS ("represents"),
        REQUIRES ("requires"),
        SIGNALS ("signals"),
        SIGNALS_ONLY ("signals_only"),

        // quantifiers and "generalized quantifiers"
        FORALL ("\\forall"),
        EXISTS ("\\exists"),
        BSUM ("\\bsum"),
        MIN ("\\min"),
        MAX ("\\max"),
        NUM_OF ("\\num_of"),
        PRODUCT ("\\product"),
        SUM ("\\sum"),

        // ADT stuff
        SEQ_DEF ("\\seq_def"),
        STORE_REF_EXPR("store_ref_expr"),
        CREATE_LOCSET("create locset"),
        PAIRWISE_DISJOINT("\\disjoint"),
        EMPTY ("\\empty"),
        UNION ("\\set_union"),
        INTERSECT ("\\intersect"),
        SINGLETON ("\\singleton"),
        SETMINUS ("\\set_minus"),
        UNIONINF ("\\infinite_union"),
        DISJOINT ("\\disjoint"),
        SUBSET ("\\subset"),

        // logical operators
        EQUIVALENCE ("<==>"),
        ANTIVALENCE ("<=!=>"),
        EQ ("=="),
        NEQ ("!="),
        NOT_MOD ("\\not_modified"),
        VALUES ("\\values"),
        INDEX ("\\index"),
        INDEX_OF ("\\seq_indexOf"),
        SEQ_GET ("\\seq_get"),
        SEQ_CONCAT ("\\seq_concat"),
        REACH ("reach"),
        REACH_LOCS ("reachLocs"),
        COMMENTARY ("(* *)"),
        DL ("\\dl_"),

        // arithmetic
        ADD ("+"),
        SUBTRACT ("-"),
        SHIFT_LEFT ("<<"),
        SHIFT_RIGHT (">>"),
        UNSIGNED_SHIFT_RIGHT (">>>"),
        BREAKS ("breaks"),
        CONTINUES ("continues"),
        RETURNS ("returns");

        private final String jmlName;
        JMLKeyWord(String name) {
            jmlName = name;
        }


        public String jmlName() {
            return jmlName;
        }

        @Override
        public String toString(){
            return jmlName;
        }


        public static JMLKeyWord jmlValueOf(String jmlName)
                throws IllegalArgumentException {
            for (JMLKeyWord keyWord : JMLKeyWord.values()) {
                if (keyWord.jmlName().equals(jmlName)) {
                    return keyWord;
                }
            }
            return null;
        }
    }

    public JMLTranslator(SLTranslationExceptionManager excManager, TermServices services) {
        this(excManager,null,services);
    }

    public JMLTranslator(SLTranslationExceptionManager excManager,
                         String fileName,
                         TermServices services) {
        this.excManager = excManager;
        this.services = services;
        this.tb = services.getTermBuilder();
        this.fileName = fileName;

        translationMethods =
                new EnumMap<JMLKeyWord, JMLTranslationMethod>(JMLKeyWord.class) {

                    private static final long serialVersionUID = 1L;

                    public JMLTranslationMethod get(Object key) {
                        JMLTranslationMethod m = super.get(key);
                        if (m != null) {
                            return m;
                        } else {
                            throw new IllegalArgumentException(key.toString());
                        }
                    }
                };

        // clauses
        translationMethods.put(JMLKeyWord.ACCESSIBLE,
                               new JMLTranslationMethod() {

            @Override
            public Term translate(SLTranslationExceptionManager excManager,
                                  Object... params)
                    throws SLTranslationException {
                checkParameters(params, Term.class, Services.class);
                Term ensuresTerm = (Term) params[0];
                Services services = (Services) params[1];

                BooleanLDT booleanLDT =
                        services.getTypeConverter().getBooleanLDT();
                if (ensuresTerm.sort() == booleanLDT.targetSort()) {
                    return tb.convertToFormula(ensuresTerm);
                } else {
                    return ensuresTerm;
                }
            }
        });
        translationMethods.put(JMLKeyWord.ASSIGNABLE,
                               new JMLTranslationMethod() {

            @Override
            public Term translate(SLTranslationExceptionManager excManager,
                                  Object... params)
                    throws SLTranslationException {
                checkParameters(params, Term.class, Services.class);
                Term ensuresTerm = (Term) params[0];
                Services services = (Services) params[1];

                BooleanLDT booleanLDT =
                        services.getTypeConverter().getBooleanLDT();
                if (ensuresTerm.sort() == booleanLDT.targetSort()) {
                    return tb.convertToFormula(ensuresTerm);
                } else {
                    return ensuresTerm;
                }
            }
        });
        translationMethods.put(JMLKeyWord.DEPENDS,
                               new JMLTranslationMethod() {

            @Override
            public Triple<IObserverFunction, Term, Term> translate(
                    SLTranslationExceptionManager excManager,
                                    Object... params)
                    throws SLTranslationException {
                checkParameters(params, SLExpression.class, Term.class,
                                SLExpression.class, Services.class);
                SLExpression lhs = (SLExpression) params[0];
                Term rhs = (Term) params[1];
                SLExpression mby = (SLExpression) params[2];
                Services services = (Services) params[3];

                LocationVariable heap =
                        services.getTypeConverter().getHeapLDT().getHeap();
                if (!lhs.isTerm()
                    || !(lhs.getTerm().op() instanceof IObserverFunction)
                    || lhs.getTerm().sub(0).op() != heap) {
                    throw excManager.createException("Depends clause with unexpected lhs: " + lhs);
                }
                return new Triple<IObserverFunction, Term, Term>(
                        (IObserverFunction) lhs.getTerm().op(),
                        rhs,
                        mby == null ? null : mby.getTerm());
            }
        });
        translationMethods.put(JMLKeyWord.ENSURES, new JMLTranslationMethod() {

            @Override
            public Term translate(SLTranslationExceptionManager excManager,
                                  Object... params)
                    throws SLTranslationException {
                checkParameters(params, Term.class, Services.class);
                Term ensuresTerm = (Term) params[0];
                TermServices services = (TermServices) params[1];
                return tb.convertToFormula(ensuresTerm);
            }
        });
        translationMethods.put(JMLKeyWord.MODEL_METHOD_AXIOM, new JMLTranslationMethod() {

        	@Override
        	public Term translate(SLTranslationExceptionManager excManager, Object... params)
        	              throws SLTranslationException {
        	    checkParameters(params, Term.class, Services.class);
        	    Term axiomsTerm = (Term) params[0];
        	    TermServices services = (TermServices) params[1];
        	    return tb.convertToFormula(axiomsTerm);
        	}
       });
       translationMethods.put(JMLKeyWord.REPRESENTS,
                               new JMLTranslationMethod() {

            @Override
            public Pair<IObserverFunction, Term> translate(SLTranslationExceptionManager excManager,
                                                           Object... params)
                    throws SLTranslationException {
                checkParameters(params, SLExpression.class, Term.class,
                                Services.class);
                SLExpression lhs = (SLExpression) params[0];
                Term t = (Term) params[1];

                return new Pair<IObserverFunction, Term>(
                        (IObserverFunction) lhs.getTerm().op(),
                        t);
            }
        });
        translationMethods.put(JMLKeyWord.REQUIRES, new JMLTranslationMethod() {

            @Override
            public Term translate(SLTranslationExceptionManager excManager,
                                  Object... params)
                    throws SLTranslationException {
                checkParameters(params, Term.class, Services.class);
                Term requiresTerm = (Term) params[0];
                TermServices services = (TermServices) params[1];
                return tb.convertToFormula(requiresTerm);
            }
        });
        translationMethods.put(JMLKeyWord.SIGNALS, new JMLTranslationMethod() {

            @Override
            public Term translate(SLTranslationExceptionManager excManager,
                                  Object... params)
                    throws SLTranslationException {
                checkParameters(params, Term.class, LogicVariable.class,
                                ProgramVariable.class, KeYJavaType.class,
                                Services.class);
                Term result = (Term) params[0];
                LogicVariable eVar = (LogicVariable) params[1];
                ProgramVariable excVar = (ProgramVariable) params[2];
                KeYJavaType excType = (KeYJavaType) params[3];
                TermServices services = (TermServices) params[4];

                if (result == null) {
                    result = tb.tt();
                } else {
                    Map /* Operator -> Operator */ replaceMap =
                            new LinkedHashMap();
                    replaceMap.put(eVar, excVar);
                    OpReplacer excVarReplacer = new OpReplacer(replaceMap, services.getTermFactory());

                    Sort os = excType.getSort();
                    Function instance = os.getInstanceofSymbol(services);

                    result = tb.imp(
                            tb.equals(tb.func(instance, tb.var(excVar)), tb.TRUE()),
                            tb.convertToFormula(excVarReplacer.replace(result)));
                }
                return result;
            }
        });
        translationMethods.put(JMLKeyWord.SIGNALS_ONLY,
                               new JMLTranslationMethod() {

            @Override
            public Term translate(SLTranslationExceptionManager excManager,
                                  Object... params)
                    throws SLTranslationException {
                checkParameters(params,
                                ImmutableList.class, ProgramVariable.class,
                                Services.class);
                ImmutableList<KeYJavaType> signalsonly =
                        (ImmutableList<KeYJavaType>) params[0];
                ProgramVariable excVar = (ProgramVariable) params[1];
                TermServices services = (TermServices) params[2];
                // Build appropriate term out of the parsed list of types
                // i.e. disjunction of "excVar instanceof ExcType"
                // for every ExcType in the list
                Term result = tb.ff();

                Iterator<KeYJavaType> it = signalsonly.iterator();
                while (it.hasNext()) {
                    KeYJavaType kjt = it.next();
                    Function instance = kjt.getSort().getInstanceofSymbol(
                            services);
                    result = tb.or(result,
                                   tb.equals(
                            tb.func(instance, tb.var(excVar)),
                            tb.TRUE()));
                }

                return result;
            }
        });
        translationMethods.put(JMLKeyWord.BREAKS, new JMLTranslationMethod() {

            @Override
            public Pair<Label, Term> translate(SLTranslationExceptionManager excManager, Object... params) throws SLTranslationException {
                checkParameters(params, Term.class, String.class, Services.class);
                Term term = (Term) params[0];
                String label = (String) params[1];
                TermServices services = (TermServices) params[2];
                Term formula = term == null ? tb.tt() : tb.convertToFormula(term);
                return new Pair<Label, Term>(label == null ? null : new ProgramElementName(label), formula);
            }
        });
        translationMethods.put(JMLKeyWord.CONTINUES, new JMLTranslationMethod() {

            @Override
            public Pair<Label, Term> translate(SLTranslationExceptionManager excManager,
                                  Object... params)
                    throws SLTranslationException {
                checkParameters(params, Term.class, String.class, Services.class);
                Term term = (Term) params[0];
                String label = (String) params[1];
                TermServices services = (TermServices) params[2];
                Term formula = term == null ? tb.tt() : tb.convertToFormula(term);
                return new Pair<Label, Term>(label == null ? null : new ProgramElementName(label), formula);
            }
        });
        translationMethods.put(JMLKeyWord.RETURNS, new JMLTranslationMethod() {

            @Override
            public Term translate(SLTranslationExceptionManager excManager,
                                  Object... params)
                    throws SLTranslationException {
                checkParameters(params, Term.class, Services.class);
                Term term = (Term) params[0];
                TermServices services = (TermServices) params[1];
                return term == null ? tb.tt() : tb.convertToFormula(term);
            }
        });

        // quantifiers
        translationMethods.put(JMLKeyWord.FORALL,
                               new JMLQuantifierTranslationMethod() {

            @Override
            public Term translateQuantifier(QuantifiableVariable qv,
                                            Term t)
                    throws SLTranslationException {
                return tb.all(qv, t);
            }


            @Override
            public Term combineQuantifiedTerms(Term t1,
                                               Term t2)
                    throws SLTranslationException {
                return tb.imp(t1, t2);
            }


            @Override
            protected boolean isGeneralized() {
                return false;
            }
        });
        translationMethods.put(JMLKeyWord.EXISTS,
                               new JMLQuantifierTranslationMethod() {

            @Override
            public Term translateQuantifier(QuantifiableVariable qv,
                                            Term t)
                    throws SLTranslationException {
                return tb.ex(qv, t);
            }


            @Override
            public Term combineQuantifiedTerms(Term t1,
                                               Term t2)
                    throws SLTranslationException {
                return tb.andSC(t1, t2);
            }


            @Override
            protected boolean isGeneralized() {
                return false;
            }
        });
        translationMethods.put(JMLKeyWord.BSUM, new JMLTranslationMethod() {
            // TODO: the bsum keyword in JML is deprecated

            @SuppressWarnings("unchecked")
            @Override
            public SLExpression translate(
                    SLTranslationExceptionManager excManager,
                    Object... params)
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
                Services services = (Services) params[5];
                KeYJavaType promo = t.getType();
                    // services.getTypeConverter().getPromotedType(declsType, t.getType());

                if (!(declsType.getJavaType().equals(PrimitiveType.JAVA_INT)
                        || declsType.getJavaType().equals(PrimitiveType.JAVA_BIGINT))) {
                    throw new SLTranslationException("bounded sum variable must be of type int or \\bigint");
                } else if (declVars.size() != 1) {
                    throw new SLTranslationException(
                            "bounded sum must declare exactly one variable");
                }
                LogicVariable qv = declVars.head();
                Term resultTerm = tb.bsum(qv, a.getTerm(), b.getTerm(), t.getTerm(), services);
                warnings.add(new PositionedString("The keyword \\bsum is deprecated and will be removed in the future.\n" +
                		"Please use the standard \\sum syntax."));
                final SLExpression bsumExpr = new SLExpression(resultTerm, promo);
                final JavaIntegerSemanticsHelper jish = new JavaIntegerSemanticsHelper(services, excManager);
                // cast to specific JML type (fixes bug #1347)
                return jish.buildCastExpression(promo, bsumExpr);
            }
        });
        translationMethods.put(JMLKeyWord.SUM,
                               new JMLBoundedNumericalQuantifierTranslationMethod() {

            @Override
            public Term translateBoundedNumericalQuantifier(
                    QuantifiableVariable qv,
                    Term lo,
                    Term hi,
                    Term body) {
                return tb.bsum(qv, lo, hi, body, services);
            }

            @Override
            protected Term translateUnboundedNumericalQuantifier(
                    KeYJavaType declsType, boolean nullable,
                    ImmutableList<QuantifiableVariable> qvs, Term range,
                    Term body) {
                final Term tr = typerestrict(declsType,nullable,qvs,services);
                return tb.sum(qvs, tb.andSC(tr,range), body, services);
            }

        });

        translationMethods.put(JMLKeyWord.PRODUCT,
                new JMLBoundedNumericalQuantifierTranslationMethod() {

            @Override
            public Term translateBoundedNumericalQuantifier(
                    QuantifiableVariable qv,
                    Term lo,
                    Term hi,
                    Term body) {
                return tb.bprod(qv, lo, hi, body, services);
            }

            @Override
            protected Term translateUnboundedNumericalQuantifier(
                    KeYJavaType declsType, boolean nullable,
                    ImmutableList<QuantifiableVariable> qvs, Term range,
                    Term body) {
                final Term tr = typerestrict(declsType,nullable,qvs,services);
                return tb.prod(qvs, tb.andSC(tr,range), body, services);
            }

        });

        translationMethods.put(JMLKeyWord.MIN,
                               new JMLTranslationMethod() {


            // TODO: make subtype of JMLBoundedNumericalQuantifierTranslationMethod and remove this
            private Term typerestrict(KeYJavaType kjt, final boolean nullable, Iterable<QuantifiableVariable> qvs, Services services) {
                final Type type = kjt.getJavaType();
                final int arrayDepth = JMLSpecExtractor.arrayDepth(type, services);
                Term res = tb.tt();
                for (QuantifiableVariable qv: qvs) {
                    if (type instanceof PrimitiveType) {
                        if (type == PrimitiveType.JAVA_BYTE) res = tb.and(res,tb.inByte(tb.var(qv)));
                        if (type == PrimitiveType.JAVA_SHORT) res = tb.and(res,tb.inShort(tb.var(qv)));
                        if (type == PrimitiveType.JAVA_CHAR) res = tb.and(res,tb.inChar(tb.var(qv)));
                        if (type == PrimitiveType.JAVA_INT) res = tb.and(res,tb.inInt(tb.var(qv)));
                        if (type == PrimitiveType.JAVA_LONG) res = tb.and(res,tb.inLong(tb.var(qv)));
                    } else {
                        // assume reference type
                        if (nullable) {
                            res = tb.and(res,tb.created(tb.var(qv)));
                        } else {
                            final Term nonNull = arrayDepth > 0 ?
                                    tb.deepNonNull(tb.var(qv), tb.zTerm(arrayDepth))
                                    : tb.not(tb.equals(tb.var(qv), tb.NULL()));
                            res = tb.and(res, tb.and(
                                    tb.created(tb.var(qv)), nonNull));
                        }
                    }
                }
                return res;
            }

            
            @Override
            public Object translate(
                    SLTranslationExceptionManager excManager,
                    Object... params)
                            throws SLTranslationException {
                checkParameters(params, Term.class, Term.class, KeYJavaType.class, ImmutableList.class, Boolean.class, KeYJavaType.class, Services.class);
                final Services services = (Services) params[6];
                Term guard = tb.convertToFormula((Term) params[0]);
                assert guard.sort() == Sort.FORMULA;
                final Term body = (Term) params[1];
                final KeYJavaType declsType = (KeYJavaType) params[2];
                final boolean nullable = (Boolean) params[4];
                @SuppressWarnings("unchecked")
                final ImmutableList<QuantifiableVariable> qvs = (ImmutableList<QuantifiableVariable>) params[3];
                final Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();
                if (body.sort() != intSort)
                    throw excManager.createException("body of \\min expression must be integer type");
                final Term tr = typerestrict(declsType,nullable,qvs,services);
                final Term min = tb.min(qvs, tb.andSC(tr, guard), body, services);
                final KeYJavaType type = services.getTypeConverter().getKeYJavaType(PrimitiveType.JAVA_BIGINT);

                final SLExpression result = new SLExpression(min,type);

                return result;
            }


        });
        translationMethods.put(JMLKeyWord.MAX,
                new JMLTranslationMethod() {

            // TODO: make subtype of JMLBoundedNumericalQuantifierTranslationMethod and remove this
            private Term typerestrict(KeYJavaType kjt, final boolean nullable, Iterable<QuantifiableVariable> qvs, Services services) {
                final Type type = kjt.getJavaType();
                final int arrayDepth = JMLSpecExtractor.arrayDepth(type, services);
                Term res = tb.tt();
                for (QuantifiableVariable qv: qvs) {
                    if (type instanceof PrimitiveType) {
                        if (type == PrimitiveType.JAVA_BYTE) res = tb.and(res,tb.inByte(tb.var(qv)));
                        if (type == PrimitiveType.JAVA_SHORT) res = tb.and(res,tb.inShort(tb.var(qv)));
                        if (type == PrimitiveType.JAVA_CHAR) res = tb.and(res,tb.inChar(tb.var(qv)));
                        if (type == PrimitiveType.JAVA_INT) res = tb.and(res,tb.inInt(tb.var(qv)));
                        if (type == PrimitiveType.JAVA_LONG) res = tb.and(res,tb.inLong(tb.var(qv)));
                    } else {
                        // assume reference type
                        if (nullable) {
                            res = tb.and(res,tb.created(tb.var(qv)));
                        } else {
                            final Term nonNull = arrayDepth > 0 ?
                                    tb.deepNonNull(tb.var(qv), tb.zTerm(arrayDepth))
                                    : tb.not(tb.equals(tb.var(qv), tb.NULL()));
                            res = tb.and(res, tb.and(
                                    tb.created(tb.var(qv)), nonNull));
                        }
                    }
                }
                return res;
            }
            
            @Override
            public Object translate(
                    SLTranslationExceptionManager excManager,
                    Object... params)
                            throws SLTranslationException {
                checkParameters(params, Term.class, Term.class, KeYJavaType.class, ImmutableList.class, Boolean.class, KeYJavaType.class, Services.class);
                final Services services = (Services) params[6];
                Term guard = tb.convertToFormula((Term) params[0]);
                final Term body = (Term) params[1];
                final KeYJavaType declsType = (KeYJavaType) params[2];
                final boolean nullable = (Boolean) params[4];
                @SuppressWarnings("unchecked")
                final ImmutableList<QuantifiableVariable> qvs = (ImmutableList<QuantifiableVariable>) params[3];
                final Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();
                if (body.sort() != intSort)
                    throw excManager.createException("body of \\max expression must be integer type");
                final Term tr = typerestrict(declsType,nullable,qvs,services);
                final Term max = tb.max(qvs, tb.andSC(tr, guard), body, services);
                final KeYJavaType type = services.getTypeConverter().getKeYJavaType(PrimitiveType.JAVA_BIGINT);

                final SLExpression result = new SLExpression(max,type);

                return result;
            }

        });

        translationMethods.put(JMLKeyWord.SEQ_DEF, new JMLTranslationMethod() {

            @Override
            public SLExpression translate(
                    SLTranslationExceptionManager excManager,
                    Object... params)
                    throws SLTranslationException {
                checkParameters(params,
                                SLExpression.class, SLExpression.class,
                                SLExpression.class, KeYJavaType.class,
                                ImmutableList.class, Services.class);
                SLExpression a = (SLExpression) params[0];
                SLExpression b = (SLExpression) params[1];
                SLExpression t = (SLExpression) params[2];
                KeYJavaType declsType = (KeYJavaType) params[3];
                @SuppressWarnings("unchecked")
                ImmutableList<LogicVariable> declVars =
                        (ImmutableList<LogicVariable>) params[4];
                Services services = (Services) params[5];

                if (!(declsType.getJavaType().equals(PrimitiveType.JAVA_INT)
                        || declsType.getJavaType().equals(PrimitiveType.JAVA_BIGINT))) {
                    throw new SLTranslationException("sequence definition variable must be of type int or \\bigint");
                } else if (declVars.size() != 1) {
                    throw new SLTranslationException(
                            "sequence definition must declare exactly one variable");
                }
                LogicVariable qv = declVars.head();
                Term tt = t.getTerm();
                if (tt.sort() == Sort.FORMULA) {
                    // bugfix (CS): t.getTerm() delivers a formula instead of a
                    // boolean term; obviously the original boolean terms are
                    // converted to formulas somewhere else; however, we need
                    // boolean terms instead of formulas here
                    tt = tb.convertToBoolean(t.getTerm());
                }
                Term resultTerm = tb.seqDef(qv, a.getTerm(), b.getTerm(), tt);
                final KeYJavaType seqtype =
                        services.getJavaInfo().getPrimitiveKeYJavaType("\\seq");
                return new SLExpression(resultTerm, seqtype);
            }
        });

        translationMethods.put(JMLKeyWord.NUM_OF,
                               new JMLBoundedNumericalQuantifierTranslationMethod() {

            @Override
            public Term translateBoundedNumericalQuantifier(
                    QuantifiableVariable qv,
                    Term lo,
                    Term hi,
                    Term body) {
                final Term cond = tb.ife(tb.convertToFormula(body),
                                         tb.one(), tb.zero());
                return tb.bsum(qv, lo, hi, cond, services);
            }

            @Override
            protected Term translateUnboundedNumericalQuantifier(
                    KeYJavaType declsType, boolean nullable,
                    ImmutableList<QuantifiableVariable> qvs, Term range,
                    Term body) {
                final Term tr = typerestrict(declsType,nullable,qvs,services);
                final Term cond = tb.ife(tb.convertToFormula(body),
                        tb.one(), tb.zero());
                return tb.sum(qvs, tb.andSC(tr,range), cond, services);
            }

        });

        // primary expressions
        translationMethods.put(JMLKeyWord.INV, new JMLTranslationMethod() {

            /** Need to handle this one differently from INV_FOR
             * since here also static invariants may occur.
             * For a static invariant, take the passed type as receiver.
             */
            @Override
            public Object translate(SLTranslationExceptionManager excManager,
                    Object... params) throws SLTranslationException {
                checkParameters(params, Services.class, Term.class, KeYJavaType.class);
                final TermServices services = (TermServices)params[0];
                final Term selfVar = (Term)params[1];
                final KeYJavaType targetType = (KeYJavaType)params[2];
                final boolean isStatic = selfVar == null;
                assert targetType != null || !isStatic;
                final Term result = isStatic? tb.staticInv(targetType): tb.inv(selfVar);
                return new SLExpression(result);
            }});

        translationMethods.put(JMLKeyWord.INV_FOR,
                               new JMLTranslationMethod() {

            @Override
            public SLExpression translate(
                    SLTranslationExceptionManager excManager,
                    Object... params)
                    throws SLTranslationException {
                checkParameters(params, Services.class, SLExpression.class);
                final Services services = (Services)params[0];
                IObserverFunction inv = services.getJavaInfo().getInv();
                Term obj = ((SLExpression) params[1]).getTerm();
                return new SLExpression(tb.func(inv, tb.getBaseHeap(), obj));
            }
        });

//        translationMethods.put(JMLKeyWord.NOT_MOD, new JMLPostExpressionTranslationMethod(){
//
//            @Override
//            protected String name() {
//                return "\\not_modified";
//            }
//
//            /**
//             * @param services Services
//             * @param heapAtPre The pre-state heap (since we are in a post-condition)
//             * @param params Must be of length 1 with a Term (store-ref expression)
//             */
//            @Override
//            protected Term translate(Services services, Term heapAtPre, Object[] params) throws SLTranslationException {
//                checkParameters(params, Term.class);
//                Term t = (Term) params[0];
//
//                // collect variables from storereflist
//                java.util.List<Term> storeRefs = new java.util.ArrayList<Term>();
//                final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
//                final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
//                while (t.op() == ldt.getUnion()){
//                    storeRefs.add(t.sub(0));
//                    t = t.sub(1);
//                }
//                storeRefs.add(t);
//                // construct equality predicates
//                Term res = TB.tt();
//                for (Term sr: storeRefs){
//                    if (sr.op() == ldt.getSingleton()){
//                        final Term ref = TB.dot(services, Sort.ANY, sr.sub(0), sr.sub(1));
//                        res = TB.and(res, TB.equals(ref,convertToOld(services, heapAtPre, ref)));
//                    } else if (sr.op() == ldt.getEmpty()){
//                        // do nothing
//                    } else if (sr.op().equals(ldt.getSetMinus()) && sr.sub(0).op().equals(ldt.getAllLocs()) && sr.sub(1).op().equals(ldt.getFreshLocs())){
//                        // this is the case for "\everything"
//                        final JavaInfo ji = services.getJavaInfo();
//                        final LogicVariable fld = new LogicVariable(new Name("f"), heapLDT.getFieldSort());
//                        final LogicVariable obj = new LogicVariable(new Name("o"), ji.objectSort());
//                        final Term objTerm = TB.var(obj);
//                        final Term fldTerm = TB.var(fld);
//                        final Term ref = TB.dot(services, Sort.ANY, objTerm, fldTerm);
//                        final Term fresh = TB.subset(services, TB.singleton(services, objTerm, fldTerm ), TB.freshLocs(services, heapAtPre));
//                        final Term bodyTerm = TB.or(TB.equals(ref, convertToOld(services, heapAtPre, ref)),fresh);
//                        res = TB.and(res, TB.all(fld, TB.all(obj, bodyTerm)));
//                    } else {
//                        // all other results are not meant to occur
//                        throw new SLTranslationException("Term "+sr+" is not a valid store-ref expression.");
//                    }
//                }
//                return res;
//            }
//
//        });


        translationMethods.put(JMLKeyWord.INDEX_OF, new JMLTranslationMethod() {

            @Override
            public Object translate(SLTranslationExceptionManager excManager,
                                    Object... params)
                    throws SLTranslationException {
                checkParameters(params, Services.class, SLExpression.class, SLExpression.class);
                final Services services = (Services)params[0];
                final Term seq = ((SLExpression)params[1]).getTerm();
                final Term elem = ((SLExpression)params[2]).getTerm();
                final KeYJavaType inttype = services.getJavaInfo().getPrimitiveKeYJavaType(PrimitiveType.JAVA_BIGINT);
                return new SLExpression(tb.indexOf(seq,elem),inttype);
            }
        });

        translationMethods.put(JMLKeyWord.SEQ_GET, new JMLTranslationMethod() {

            @Override
            public Object translate(SLTranslationExceptionManager excManager,
                                    Object... params)
                    throws SLTranslationException {
                checkParameters(params, Services.class, SLExpression.class,
                                SLExpression.class);
                final TermServices services = (TermServices) params[0];
                final Term seq = ((SLExpression) params[1]).getTerm();
                final Term idx = ((SLExpression) params[2]).getTerm();
                return new SLExpression(tb.seqGet(Sort.ANY, seq, idx));
            }
        });

        translationMethods.put(JMLKeyWord.SEQ_CONCAT,
                               new JMLTranslationMethod() {

            @Override
            public Object translate(SLTranslationExceptionManager excManager,
                                    Object... params)
                    throws SLTranslationException {
                checkParameters(params, Services.class, SLExpression.class,
                                SLExpression.class);
                final Services services = (Services) params[0];
                final Term seq1 = ((SLExpression) params[1]).getTerm();
                final Term seq2 = ((SLExpression) params[2]).getTerm();
                final KeYJavaType seqtype =
                        services.getJavaInfo().getPrimitiveKeYJavaType("\\seq");
                return new SLExpression(tb.seqConcat(seq1, seq2),
                                        seqtype);
            }
        });

        translationMethods.put(JMLKeyWord.REACH,
                               new JMLFieldAccessExpressionTranslationMethod() {

            @Override
            public Object translate(SLTranslationExceptionManager excManager,
                                    Object... params)
                    throws SLTranslationException {
                checkParameters(params, Term.class, SLExpression.class,
                                SLExpression.class, SLExpression.class,
                                Services.class);
                final Term t = (Term) params[0];
                final SLExpression e1 = (SLExpression) params[1];
                final SLExpression e2 = (SLExpression) params[2];
                final SLExpression e3 = (SLExpression) params[3];
                final Services services = (Services) params[4];
                final LogicVariable stepsLV = e3 == null
                                              ? new LogicVariable(new Name("n"),
                                                                  services.getTypeConverter().getIntegerLDT().targetSort())
                        : null;
                final Term h = tb.getBaseHeap();
                final Term s = getFields(excManager, t, services);
                final Term o = e1.getTerm();
                final Term o2 = e2.getTerm();
                final Term n = e3 == null ? tb.var(stepsLV) : e3.getTerm();
                Term reach = tb.reach(h, s, o, o2, n);
                if (e3 == null) {
                    reach = tb.ex(stepsLV, reach);
                }
                return new SLExpression(reach);
            }
        });

        translationMethods.put(JMLKeyWord.REACH_LOCS,
                               new JMLFieldAccessExpressionTranslationMethod() {

            @Override
            public Object translate(SLTranslationExceptionManager excManager,
                                    Object... params)
            throws SLTranslationException {
                checkParameters(params, Term.class, SLExpression.class,
                                SLExpression.class, Services.class);
                final Term t = (Term) params[0];
                final SLExpression e1 = (SLExpression) params[1];
                final SLExpression e3 = (SLExpression) params[2];
                final Services services = (Services) params[3];
                final LogicVariable objLV =
                        new LogicVariable(new Name("o"),
                                          services.getJavaInfo().objectSort());
                final LogicVariable stepsLV = e3 == null
                                              ? new LogicVariable(new Name("n"),
                                                                  services.getTypeConverter().getIntegerLDT().targetSort())
                        : null;
                final Term h = tb.getBaseHeap();
                final Term s = getFields(excManager, t, services);
                final Term o = e1.getTerm();
                final Term o2 = tb.var(objLV);
                final Term n = e3 == null ? tb.var(stepsLV) : e3.getTerm();
                Term reach = tb.reach(h, s, o, o2, n);
                if (e3 == null) {
                    reach = tb.ex(stepsLV, reach);
                }

                final LogicVariable fieldLV
                = new LogicVariable(new Name("f"), services.getTypeConverter().getHeapLDT().getFieldSort());
                final Term locSet
                = tb.guardedSetComprehension(new LogicVariable[]{objLV, fieldLV},
                        reach,
                        o2,
                        tb.var(fieldLV));

                return new SLExpression(locSet, services.getJavaInfo().getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
            }
        });

        translationMethods.put(JMLKeyWord.FRESH,
                               new JMLTranslationMethod() {

            @Override
            public SLExpression translate(
                    SLTranslationExceptionManager excManager,
                    Object... params)
                    throws SLTranslationException {
                checkParameters(params,
                                ImmutableList.class, 
                                Map.class,
                                Services.class);
                final ImmutableList<SLExpression> list = (ImmutableList) params[0];
                final Map<LocationVariable,Term> atPres = (Map) params[1];
                final Services services = (Services) params[2];
                final LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();

	        if(atPres == null || atPres.get(baseHeap) == null) {
	            throw excManager.createException("\\fresh not allowed in this context");
	        }

	        Term t = tb.tt();
	        final Sort objectSort = services.getJavaInfo().objectSort();
                final TypeConverter tc = services.getTypeConverter();
	        for(SLExpression expr: list) {
    	            if(!expr.isTerm()) {
	                throw excManager.createException("Expected a term, but found: " + expr);
	            } else if(expr.getTerm().sort().extendsTrans(objectSort)) {
	                t = tb.and(t,
	                           tb.equals(tb.select(tc.getBooleanLDT().targetSort(),
	                                           atPres.get(baseHeap),
	                                           expr.getTerm(),
	                                           tb.func(tc.getHeapLDT().getCreated())),
	                                 tb.FALSE()));
                        // add non-nullness (bug #1364)
                        t = tb.and(t, tb.not(tb.equals(expr.getTerm(),tb.NULL())));
    	            } else if(expr.getTerm().sort().extendsTrans(tc.getLocSetLDT().targetSort())) {
	            t = tb.and(t, tb.subset(expr.getTerm(),
	                                    tb.freshLocs(atPres.get(baseHeap))));
	            } else {
	                throw excManager.createException("Wrong type: " + expr);
	            }
	        }
	        return new SLExpression(t);
            }
        });

        // operators
        translationMethods.put(JMLKeyWord.EQUIVALENCE,
                               new JMLEqualityTranslationMethod() {

            @Override
            public SLExpression translate(
                    SLTranslationExceptionManager excManager,
                    Object... params)
                    throws SLTranslationException {
                checkParameters(params,
                                SLExpression.class, SLExpression.class,
                                Services.class);
                SLExpression expr1 = (SLExpression) params[0];
                SLExpression expr2 = (SLExpression) params[1];
                Services services = (Services) params[2];

                checkSLExpressions(expr1, expr2, excManager, "<==>");
                return buildEqualityTerm(expr1, expr2, excManager, services);
            }
        });
        translationMethods.put(JMLKeyWord.ANTIVALENCE,
                               new JMLEqualityTranslationMethod() {

            @Override
            public SLExpression translate(
                    SLTranslationExceptionManager excManager,
                    Object... params)
                    throws SLTranslationException {
                checkParameters(params,
                                SLExpression.class, SLExpression.class,
                                Services.class);
                SLExpression expr1 = (SLExpression) params[0];
                SLExpression expr2 = (SLExpression) params[1];
                Services services = (Services) params[2];

                checkSLExpressions(expr1, expr2, excManager, "<=!=>");
                SLExpression eq =
                        buildEqualityTerm(expr1, expr2, excManager, services);
                return new SLExpression(tb.not(eq.getTerm()));
            }
        });
        translationMethods.put(JMLKeyWord.EQ,
                               new JMLEqualityTranslationMethod() {

            @Override
            public SLExpression translate(
                    SLTranslationExceptionManager excManager,
                    Object... params)
                    throws SLTranslationException {
                checkParameters(params,
                                SLExpression.class, SLExpression.class,
                                Services.class);
                SLExpression expr1 = (SLExpression) params[0];
                SLExpression expr2 = (SLExpression) params[1];
                Services services = (Services) params[2];

                checkSLExpressions(expr1, expr2, excManager, "==");
                return buildEqualityTerm(expr1, expr2, excManager, services);
            }
        });
        translationMethods.put(JMLKeyWord.NEQ,
                               new JMLEqualityTranslationMethod() {

            @Override
            public SLExpression translate(
                    SLTranslationExceptionManager excManager,
                    Object... params)
                    throws SLTranslationException {
                checkParameters(params,
                                SLExpression.class, SLExpression.class,
                                Services.class);
                SLExpression expr1 = (SLExpression) params[0];
                SLExpression expr2 = (SLExpression) params[1];
                Services services = (Services) params[2];

                checkSLExpressions(expr1, expr2, excManager, "!=");
                SLExpression eq =
                        buildEqualityTerm(expr1, expr2, excManager, services);
                if (eq.getType() != null) {
                    return new SLExpression(tb.not(eq.getTerm()), eq.getType());
                } else {
                    return new SLExpression(tb.not(eq.getTerm()));
                }
            }
        });

        translationMethods.put(JMLKeyWord.SHIFT_RIGHT, new JMLArithmeticOperationTranslationMethod(){

            @Override
            public SLExpression translate(JavaIntegerSemanticsHelper intHelper, SLExpression a, SLExpression e)
            throws SLTranslationException {
                checkNotBigint(a);
                checkNotBigint(e);

                return intHelper.buildRightShiftExpression(a, e);
            }

            @Override
            public String opName() {
                return "shift right";
            }

        });

        translationMethods.put(JMLKeyWord.SHIFT_LEFT, new JMLArithmeticOperationTranslationMethod(){

            @Override
            public SLExpression translate(JavaIntegerSemanticsHelper intHelper, SLExpression result, SLExpression e)
            throws SLTranslationException {
                checkNotBigint(result);
                checkNotBigint(e);

                return intHelper.buildLeftShiftExpression(result, e);
            }

            @Override
            public String opName() {
                return "shift left";
            }

        });

        translationMethods.put(JMLKeyWord.UNSIGNED_SHIFT_RIGHT, new JMLArithmeticOperationTranslationMethod(){

            @Override
            public SLExpression translate(JavaIntegerSemanticsHelper intHelper, SLExpression result, SLExpression e)
            throws SLTranslationException {
                checkNotBigint(result);
                checkNotBigint(e);

                return intHelper.buildUnsignedRightShiftExpression(result, e);
            }

            @Override
            public String opName() {
                return "unsigned shift right";
            }
        });

        translationMethods.put(JMLKeyWord.ADD, new JMLArithmeticOperationTranslationMethod(){

            @Override
            public String opName() {
                return "add";
            }

            @Override
            protected SLExpression translate(JavaIntegerSemanticsHelper intHelper, SLExpression left,
                    SLExpression right) throws SLTranslationException {
                    return intHelper.buildAddExpression(left, right);
            }

        });

        translationMethods.put(JMLKeyWord.SUBTRACT, new JMLArithmeticOperationTranslationMethod(){

            @Override
            protected String opName() {
                return ("subtract");
            }

            @Override
            protected SLExpression translate(JavaIntegerSemanticsHelper intHelper, SLExpression left,
                    SLExpression right) throws SLTranslationException {
                return intHelper.buildSubExpression(left, right);
            }

        });

        translationMethods.put(JMLKeyWord.CAST, new JMLTranslationMethod(){

            @Override
            public Object translate(SLTranslationExceptionManager excManager,
                    Object... params) throws SLTranslationException {
                checkParameters(params, Services.class, JavaIntegerSemanticsHelper.class, KeYJavaType.class, SLExpression.class);
                Services services = (Services)params[0];
                JavaIntegerSemanticsHelper intHelper = (JavaIntegerSemanticsHelper)params[1];
                KeYJavaType type = (KeYJavaType)params[2];
                SLExpression result = (SLExpression)params[3];

                if (type != null) {
                    if (result.isType()) {
                        throw excManager.createException("Casting of type variables not (yet) supported.");
                    }
                    assert result.isTerm();
                    Sort origType = result.getTerm().sort();

                    if (origType == Sort.FORMULA) {
                        // This case might occur since boolean expressions
                        // get converted prematurely (see bug #1121).
                        // Just check whether there is a cast to boolean.
                        if (type != services.getTypeConverter().getBooleanType()){
                            throw excManager.createException("Cannot cast from boolean to "+type+".");
                        }
                    } else if(intHelper.isIntegerTerm(result)) {
                        result = intHelper.buildCastExpression(type, result);
                    } else {result = new SLExpression(
                            tb.cast(services, type.getSort(), result.getTerm()),
                            type);
                    }
                } else {
                    throw excManager.createException("Please provide a type to cast to.");
                }
                return result;
            }});

        translationMethods.put(JMLKeyWord.CONDITIONAL, new JMLTranslationMethod(){

            @Override
            public Object translate(SLTranslationExceptionManager excManager,
                    Object... params) throws SLTranslationException {
                checkParameters(params, Services.class, SLExpression.class, SLExpression.class, SLExpression.class);
                Services services = (Services)params[0];
                SLExpression result = (SLExpression)params[1];
                SLExpression a = (SLExpression)params[2];
                SLExpression b = (SLExpression)params[3];

                // handle cases where a and b are of sort FORMULA and boolean respectively (which are incompatible, unfortunately)
                final KeYJavaType bool = services.getTypeConverter().getBooleanType();
                Term aTerm = a.getType() == bool ? tb.convertToFormula(a.getTerm()) : a.getTerm();
                Term bTerm = b.getType() == bool ? tb.convertToFormula(b.getTerm()) : b.getTerm();

                Term ife = tb.ife(tb.convertToFormula(result.getTerm()), aTerm, bTerm);
                if(a.getType() != null && a.getType().equals(b.getType())) {
                    result = new SLExpression(ife, a.getType());
                } else {
                    result = new SLExpression(ife);
                }
                return result;
            }});

        translationMethods.put(JMLKeyWord.COMMENTARY,
                               new JMLTranslationMethod() {

            @Override
            public Object translate(SLTranslationExceptionManager excManager,
                                    Object... params)
                    throws SLTranslationException {

                checkParameters(params, Services.class, Token.class,
                        LocationVariable.class, LocationVariable.class,
                        ImmutableList.class, Term.class);

                TermServices services = (TermServices) params[0];
                Token desc = (Token) params[1];
                LocationVariable selfVar = (LocationVariable) params[2];
                LocationVariable resultVar = (LocationVariable) params[3];
                ImmutableList<LocationVariable> paramVars =
                    (ImmutableList<LocationVariable>) params[4];
                Term heapAtPre = (Term) params[5];

                // strip leading and trailing (* ... *)
                String text = desc.getText();
                text = text.substring(2, text.length() - 2);

                // prepare namespaces
                NamespaceSet namespaces = services.getNamespaces().copy();
                Namespace programVariables = namespaces.programVariables();

                if (heapAtPre != null
                    && heapAtPre.op() instanceof ProgramVariable) {
                    programVariables.add(heapAtPre.op());
                }

                if (selfVar != null) {
                    programVariables.add(selfVar);
                }

                if (resultVar != null) {
                    programVariables.add(resultVar);
                }

                if (paramVars != null) {
                    for (ProgramVariable param : paramVars) {
                        programVariables.add(param);
                    }
                }

                SLExpression result;
                try {
                    result = new SLExpression(services.getTermBuilder().parseTerm(text, namespaces));
                    return result;
                } catch (ParserException ex) {
                    throw excManager.createException("Cannot parse embedded JavaDL: "
                                                     + text, desc, ex);
                }
            }
        });

        translationMethods.put(JMLKeyWord.DL, new JMLTranslationMethod() {
            @Override
            public Object translate(SLTranslationExceptionManager excManager,
                                    Object... params)
                    throws SLTranslationException {
                checkParameters(params, Token.class, ImmutableList.class,
                                Services.class);

                Token escape = (Token) params[0];
                ImmutableList<SLExpression> list =
                        (ImmutableList<SLExpression>) params[1];
                Services services = (Services) params[2];

                // strip leading "\dl_"
                String functName = escape.getText().substring(4);
                Namespace funcs = services.getNamespaces().functions();
                Named symbol = funcs.lookup(new Name(functName));

                if (symbol != null) {
                    // Function or predicate symbol found

                    assert symbol instanceof Function : "Expecting a function symbol in this namespace";
                    Function function = (Function) symbol;

                    Term[] args;
                    if (list == null) {
                        // empty parameter list
                        args = new Term[0];
                    } else {

                        Term heap = tb.getBaseHeap();

                        // special casing "implicit heap" arguments:
                        // omitting one argument means first argument is "heap"
                        int i = 0;
                        if (function.arity() == list.size() + 1
                                && function.argSort(0) == heap.sort()) {
                            args = new Term[list.size() + 1];
                            args[i++] = heap;
                        } else {
                            args = new Term[list.size()];
                        }

                        for (SLExpression expr : list) {
                            if (!expr.isTerm()) {
                                throw new SLTranslationException("Expecting a term here, not: "
                                                                 + expr);
                            }
                            args[i++] = expr.getTerm();
                        }
                    }

                    try {
                        Term resultTerm = tb.func(function, args, null);
                        final KeYJavaType type =
                                services.getTypeConverter().getIntegerLDT().targetSort() == resultTerm.sort() ?
                                        services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BIGINT) :
                                services.getJavaInfo().getKeYJavaType(resultTerm.sort());
                        SLExpression result = type==null? new SLExpression(resultTerm) : new SLExpression(resultTerm,type);
                        return result;
                    } catch (TermCreationException ex) {
                        throw excManager.createException("Cannot create term " + function.name() +
                                "(" + MiscTools.join(args, ", ") + ")", escape, ex);
                    }

                }

                assert symbol == null;  // no function symbol found

                Namespace progVars = services.getNamespaces().programVariables();
                symbol = progVars.lookup(new Name(functName));

                if (symbol == null) {
                    throw excManager.createException("Unknown escaped symbol "
                                                     + functName, escape);
                }

                assert symbol instanceof ProgramVariable : "Expecting a program variable";
                ProgramVariable pv = (ProgramVariable) symbol;
                try {
                    Term resultTerm = tb.var(pv);
                    SLExpression result = new SLExpression(resultTerm);
                    return result;
                } catch (TermCreationException ex) {
                    throw excManager.createException("Cannot create term "
                                                     + pv.name(), escape, ex);
                }

            }
        });


        // sets
        translationMethods.put(JMLKeyWord.EMPTY, new JMLTranslationMethod() {

			@Override
			public SLExpression translate(SLTranslationExceptionManager excManager,
					Object... params) throws SLTranslationException {
				checkParameters(params,Services.class,JavaInfo.class);
				return new SLExpression(tb.empty(),
                        ((JavaInfo)params[1]).getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
			}});

        translationMethods.put(JMLKeyWord.UNION, new JMLTranslationMethod() {

			@Override
			public SLExpression translate(SLTranslationExceptionManager excManager,
					Object... params) throws SLTranslationException {
				checkParameters(params, Term.class, JavaInfo.class);
				Term t = (Term)params[0];
				return new SLExpression(t, ((JavaInfo)params[1]).getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
			}});
        translationMethods.put(JMLKeyWord.INTERSECT, new JMLTranslationMethod() {

			@Override
			public SLExpression translate(SLTranslationExceptionManager excManager,
					Object... params) throws SLTranslationException {
				checkParameters(params, Term.class, JavaInfo.class);
				Term t = (Term)params[0];
				JavaInfo javaInfo = (JavaInfo)params[1];
				return new SLExpression(t, javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
			}});

        // others
        translationMethods.put(JMLKeyWord.ARRAY_REF,
                               new JMLTranslationMethod() {

            @Override
            public SLExpression translate(
                    SLTranslationExceptionManager excManager,
                    Object... params)
            throws SLTranslationException {
                checkParameters(params, Services.class, SLExpression.class,
                                String.class, Token.class, SLExpression.class,
                                SLExpression.class);
                TermServices services = (TermServices) params[0];
                SLExpression receiver = (SLExpression) params[1];
                String fullyQualifiedName = (String) params[2];
                Token lbrack = (Token) params[3];
                SLExpression rangeFrom = (SLExpression) params[4];
                SLExpression rangeTo = (SLExpression) params[5];
                SLExpression result = null;
                try {
                    whatToDoFirst(excManager, receiver, fullyQualifiedName,
                                  lbrack);

                    //arrays
                    if (receiver.getType().getJavaType() instanceof ArrayType) {
                        result = translateArrayReference(services, receiver,
                                rangeFrom, rangeTo);

                        //sequences
                    } else {
                        result = translateSequenceReference(services, receiver,
                                rangeFrom, rangeTo);
                    }
                    return result;
                }
                catch (TermCreationException tce){
                    throw excManager.createException(tce.getMessage());
                }}

            private void whatToDoFirst(SLTranslationExceptionManager excManager,
                                       SLExpression receiver,
                                       String fullyQualifiedName,
                                       Token lbrack)
                    throws SLTranslationException {
                if (receiver == null) {
                    throw excManager.createException("Array \""
                                                     + fullyQualifiedName
                                                     + "\" not found.",
                               lbrack);
                } else if (receiver.isType()) {
                    throw excManager.createException("Error in array expression: \""
                                                     + fullyQualifiedName
                                                     + "\" is a type.", lbrack);
                } else if (!(receiver.getType().getJavaType() instanceof ArrayType
                             || receiver.getType().getJavaType().equals(
                        PrimitiveType.JAVA_SEQ))) {
                    throw excManager.createException("Cannot access "
                                                     + receiver.getTerm()
                               + " as an array.");
                }
            }

            private SLExpression translateArrayReference(TermServices services,
                                                         SLExpression receiver,
                                                         SLExpression rangeFrom,
                                                         SLExpression rangeTo) {
                SLExpression result;
                if (rangeFrom == null) {
                    // We have a star. A star includes all components of an array even
                    // those out of bounds. This makes proving easier.
                    Term t = tb.allFields(receiver.getTerm());
                    result = new SLExpression(t);
                } else if (rangeTo != null) {
                    // We have "rangeFrom .. rangeTo"
                    Term t = tb.arrayRange(receiver.getTerm(),
                            rangeFrom.getTerm(),
                            rangeTo.getTerm());
                    result = new SLExpression(t);
                } else {
                    // We have a regular array access
                    Term t = tb.dotArr(receiver.getTerm(),
                            rangeFrom.getTerm());
                    ArrayType arrayType =
                            (ArrayType) receiver.getType().getJavaType();
                    KeYJavaType elementType =
                            arrayType.getBaseType().getKeYJavaType();
                    result = new SLExpression(t, elementType);
                }
                return result;
            }


            private SLExpression translateSequenceReference(TermServices services,
                                                            SLExpression receiver,
                                                            SLExpression rangeFrom,
                                                            SLExpression rangeTo)
                    throws SLTranslationException {
                if (rangeFrom == null) {
                    // a star
                    return new SLExpression(tb.allFields(receiver.getTerm()));
                } else if (rangeTo != null) {
                        Term t = tb.seqSub(receiver.getTerm(),
                                rangeFrom.getTerm(),
                                rangeTo.getTerm());
                        return new SLExpression(t);
                    } else {
                        Term t = tb.seqGet(Sort.ANY,
                                receiver.getTerm(),
                                rangeFrom.getTerm());
                        return new SLExpression(t);
                    }
            }
        });
        translationMethods.put(JMLKeyWord.STORE_REF_EXPR,
                               new JMLTranslationMethod() {

            @Override
            public Term translate(SLTranslationExceptionManager excManager,
                                  Object... params)
                    throws SLTranslationException {
                checkParameters(params, SLExpression.class, Services.class);
                SLExpression expr = (SLExpression) params[0];
                Services services = (Services) params[1];
                if (expr.isTerm()) {
                    Term t = expr.getTerm();
                    LocSetLDT locSetLDT =
                            services.getTypeConverter().getLocSetLDT();
                    if (t.sort().equals(locSetLDT.targetSort())
                        || t.op().equals(locSetLDT.getSingleton())) {
                        return t;
                    } else {
                        JMLTranslationMethod createMethod =
                                translationMethods.get(JMLKeyWord.CREATE_LOCSET);
                        ImmutableList<SLExpression> exprList =
                                ImmutableSLList.<SLExpression>nil();
                        exprList = exprList.append(expr);
                        return (Term) createMethod.translate(excManager,
                                                             exprList, services);
//                        throw excManager.createException("Not a valid storeref expression: "
//                                                         + t);
                    }
                }
                throw excManager.createException("Not a term: " + expr);
            }
        });
        translationMethods.put(JMLKeyWord.CREATE_LOCSET,
                               new JMLTranslationMethod() {

            @Override
            public Term translate(
                    SLTranslationExceptionManager excManager,
                    Object... params)
                    throws SLTranslationException {
                checkParameters(params, ImmutableList.class, Services.class);
                @SuppressWarnings("unchecked")
                ImmutableList<SLExpression> exprList =
                        (ImmutableList<SLExpression>) params[0];
                Services services = (Services) params[1];

                ImmutableList<Term> singletons = ImmutableSLList.<Term>nil();
                for (SLExpression expr : exprList) {
                    if (expr.isTerm()) {
                        Term t = expr.getTerm();
                        LocSetLDT locSetLDT =
                                services.getTypeConverter().getLocSetLDT();
                        if (!t.op().equals(locSetLDT.getSingleton())) {
                            HeapLDT heapLDT =
                                    services.getTypeConverter().getHeapLDT();
                            if (heapLDT.getSortOfSelect(t.op()) != null) {
                                final Term objTerm = t.sub(1);
                                final Term fieldTerm = t.sub(2);
                                t = tb.singleton(objTerm, fieldTerm);
                                singletons = singletons.append(t);
                            } else if (t.op() instanceof ProgramVariable) {
                                // this case may happen with local variables
                                addIgnoreWarning("local variable in assignable clause");
                                Debug.out("Can't create a locset from local variable "+ t + ".\n" +
                                        "In this version of KeY, you do not need to put them in assignable clauses.");
                            } else {
                                throw excManager.createException("Can't create a locset from "+ t + ".");
                            }
                        } else {
                            throw excManager.createException("Can't create a locset of a singleton: "
                                                             + expr);
                        }
                    } else {
                        throw excManager.createException("Not a term: " + expr);
                    }
                }
                return tb.union(singletons);
            }
        });
        translationMethods.put(JMLKeyWord.PAIRWISE_DISJOINT,
                               new JMLTranslationMethod() {

            @Override
            public SLExpression translate(
                    SLTranslationExceptionManager excManager,
                    Object... params)
                    throws SLTranslationException {
                checkParameters(params, ImmutableList.class, Services.class);
                ImmutableList<Term> list =
                        (ImmutableList<Term>) params[0];
                TermServices services = (TermServices) params[1];

                ImmutableList<Term> disTerms = ImmutableSLList.<Term>nil();
                while (!list.isEmpty()) {
                    Term t1 = list.head();
                    list = list.tail();
                    for (Term t2 : list) {
                        Term dis = tb.disjoint(t1, t2);
                        disTerms = disTerms.append(dis);
                    }
                }
                return new SLExpression(tb.and(disTerms));
            }
        });


        // keywords in loop specifications of enhanced for loops

        translationMethods.put(JMLKeyWord.INDEX, new JMLTranslationMethod(){

			@Override
			public SLExpression translate(SLTranslationExceptionManager excManager,
					Object... params) throws SLTranslationException {
				checkParameters(params, Services.class);
				final KeYJavaType t = ((Services)params[0]).getJavaInfo()
			               .getKeYJavaType(PrimitiveType.JAVA_INT);
				return new SLExpression(tb.index(),t);
			}});

        translationMethods.put(JMLKeyWord.VALUES, new JMLTranslationMethod(){

			@Override
			public SLExpression translate(SLTranslationExceptionManager excManager,
					Object... params) throws SLTranslationException {
				checkParameters(params, Services.class);
				final KeYJavaType t = ((Services)params[0]).getJavaInfo()
			               .getKeYJavaType(PrimitiveType.JAVA_SEQ);
				return new SLExpression(tb.values(),t);
			}});
    }


    /**
     *
     */
    public static <T> T translate(PositionedString expr,
                                  KeYJavaType specInClass,
                                  ProgramVariable selfVar,
                                  ImmutableList<ProgramVariable> paramVars,
                                  ProgramVariable resultVar,
                                  ProgramVariable excVar,
                                  Map<LocationVariable,Term> atPres,
                                  Class<T> resultClass,
                                  Services services)
            throws SLTranslationException {

        final KeYJMLParser parser = new KeYJMLParser(expr, services,
                                                     specInClass, selfVar,
                                                     paramVars, resultVar,
                                                     excVar, atPres);
        Object result = null;
        try {
            result = parser.top();
            List<PositionedString> warnings = parser.getWarnings();
        } catch (antlr.ANTLRException e) {
            throw parser.getExceptionManager().convertException(e);
        }
        if (resultClass.equals(Term.class)) {
            if (expr.hasLabels()) {
                T o = castToReturnType(result, resultClass);
                assert o instanceof Term;
                Term t = (Term)o;
                t = services.getTermBuilder().label((Term)castToReturnType(result, resultClass), expr.getLabels());
                return castToReturnType(t, resultClass);
            }
        }
        return castToReturnType(result, resultClass);
    }


    <T> T translate(String jmlKeyWordName,
                           Class<T> resultClass,
                           Object... params)
            throws SLTranslationException {
        try {
            JMLKeyWord jmlKeyWord = JMLKeyWord.jmlValueOf(jmlKeyWordName);
            JMLTranslationMethod m = translationMethods.get(jmlKeyWord);
            if (m == null) {
                throw excManager.createException(
                        "Unknown JML-keyword or unknown translation for "
                        + "JML-keyword \"" + jmlKeyWordName
                        + "\". The keyword seems "
                        + "not to be supported yet.");
            }
            Object result = m.translate(excManager, params);
            resultClass.cast(result);
            return castToReturnType(result, resultClass);
        } catch (IllegalArgumentException e) {
            throw excManager.createException(
                    "Unknown JML-keyword or unknown translation for "
                    + "JML-keyword \"" + jmlKeyWordName
                    + "\". The keyword seems "
                    + "not to be supported yet.", e);
        } catch (TermCreationException e) {
            throw excManager.createException(e.getMessage(), e);
        }
    }

    <T> T translate(JMLKeyWord keyword, Class<T> resultClass, Object... params)
    throws SLTranslationException {
        return translate(keyword.toString(), resultClass, params);
    }

    SLExpression translate(String jmlKeyWordName, Object... params)
    throws SLTranslationException {
        return translate(jmlKeyWordName, SLExpression.class, params);
    }

    SLExpression translate(JMLKeyWord keyword, Object...params)
    throws SLTranslationException {
        return translate(keyword.toString(), SLExpression.class, params);
    }

    /**
     * Create a skolem term (wrapped in SLExpression) for currently unsupported JML expressions of type int.
     */
    SLExpression createSkolemExprInt(Token jmlKeyWord, Services services) {
        return skolemExprHelper(jmlKeyWord, PrimitiveType.JAVA_INT, services);
    }

    /**
     * Create a skolem term (wrapped in SLExpression) for currently unsupported JML expressions of type long.
     */
    SLExpression createSkolemExprLong(Token jmlKeyWord, Services services) {
        return skolemExprHelper(jmlKeyWord, PrimitiveType.JAVA_LONG, services);
    }

    /**
     * Create a skolem term (wrapped in SLExpression) for currently unsupported JML expressions of type \bigint.
     */
    SLExpression createSkolemExprBigint(Token jmlKeyWord, Services services) {
        return skolemExprHelper(jmlKeyWord, PrimitiveType.JAVA_BIGINT, services);
    }

    /**
     * Create a skolem term (wrapped in SLExpression) for currently unsupported JML expressions of type Object.
     */
    SLExpression createSkolemExprObject(Token jmlKeyWord, Services services) {
        assert services != null;
        final KeYJavaType objType = services.getJavaInfo().getJavaLangObject();
        assert objType != null;
        return skolemExprHelper(jmlKeyWord, objType, services);
    }

    /**
     * Create a nullary predicate (wrapped in SLExpression) for currently unsupported JML expressions of type boolean.
     */
    SLExpression createSkolemExprBool(Token jmlKeyWord) {
        addUnderspecifiedWarning(jmlKeyWord);
        final Namespace fns = services.getNamespaces().functions();
        final String shortName = jmlKeyWord.getText().replace("\\", "");
        int x = -1;
        Name name = null;
        do name = new Name(shortName+"_"+ ++x);
        while (fns.lookup(name)!=null);
        final Function sk = new Function(name,Sort.FORMULA);
        fns.add(sk);
        final Term t = tb.func(sk);
        return new SLExpression(t);
    }


    /**
     * Get non-critical warnings.
     */
    public List<PositionedString> getWarnings() {
        return new ArrayList<PositionedString>(warnings);
    }

    /**
     * Get non-critical warnings.
     */
    public String getWarningsAsString() {
        StringBuffer sb = new StringBuffer();
        for (PositionedString s: warnings) {
            sb.append(s.toString());
            sb.append("\n");
        }
        sb.deleteCharAt(sb.length()-1);
        return sb.toString();
    }


    //-------------------------------------------------------------------------
    // private methods
    //-------------------------------------------------------------------------
    private void checkParameters(Object[] params,
                                 Class<?>... classes)
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
                    + "Parameter type was: "
                    + params[i - 1].getClass().getName()
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


    private static <T> T castToReturnType(Object result,
                                          Class<T> resultClass)
            throws SLTranslationException {
        if (!resultClass.isInstance(result)) {
            throw new SLTranslationException(
                    "Return value does not match the expected return type:\n"
                    + "Return type was: " + result.getClass() + "\n"
                    + "Expected type was: " + resultClass);
        }
        return resultClass.cast(result);
    }

    private SLExpression skolemExprHelper(Token jmlKeyWord, PrimitiveType type, Services services) {
        final KeYJavaType kjt = services.getJavaInfo().getPrimitiveKeYJavaType(type);
        return skolemExprHelper(jmlKeyWord,kjt,services);
    }

    private SLExpression skolemExprHelper(Token jmlKeyWord, KeYJavaType type, TermServices services) {
        addUnderspecifiedWarning(jmlKeyWord);
        assert services != null;
        final Namespace fns = services.getNamespaces().functions();
        final Sort sort = type.getSort();
        final String shortName = jmlKeyWord.getText().replace("\\", "");
        int x = -1;
        Name name = null;
        do name = new Name(shortName+"_"+ ++x);
        while (fns.lookup(name)!= null);
        final Function sk = new Function(name,sort);
        fns.add(sk);
        final Term t = tb.func(sk);
        return new SLExpression(t,type);
    }

    /**
     * This is used for features without semantics such as labels or annotations.
     * @author bruns
     * @since 1.7.2178
     */
    void addIgnoreWarning(String feature) {
        String msg = feature + " is not supported and has been silently ignored.";
        addWarning(msg);
    }

    void addIgnoreWarning(String feature, Token t) {
        String msg = feature + " is not supported and has been silently ignored.";
        addWarning(msg,t);
    }

    /**
     * Used for features with semantics (currently) not supported in KeY/DL.
     * @param feature
     */
    private void addUnderspecifiedWarning(String feature) {
        String msg = feature + "is not supported and translated to an underspecified term or formula.";
        addWarning(msg);
    }

    private void addUnderspecifiedWarning(Token t) {
        String msg = t.getText() + "is not supported and translated to an underspecified term or formula.";
        addWarning(msg, t);
    }

    void addDeprecatedWarning(String feature) {
        addWarning("deprecated syntax: "+feature);
    }

    private void addWarning(String msg) {
        Debug.out("JML translator warning: "+msg);
        warnings.add(new PositionedString(msg, fileName));
    }

    private void addWarning(String msg, Token t) {
        Debug.out("JML translator warning: "+msg);
        warnings.add(new PositionedString(msg, t));
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
        public SLExpression translate(SLTranslationExceptionManager excManager,
                              Object... params)
                throws SLTranslationException {
            checkParameters(params,
                            Term.class, Term.class, KeYJavaType.class,
                            ImmutableList.class, Boolean.class, KeYJavaType.class, Services.class);
            Term preTerm = (Term) params[0];
            Term bodyTerm = (Term) params[1];
            KeYJavaType declsType = (KeYJavaType) params[2];
            final Type type = declsType.getJavaType();
            services = (Services) params[6];
            assert services != null;
            final int arrayDepth = JMLSpecExtractor.arrayDepth(type, services);
            ImmutableList<LogicVariable> declVars =
                    (ImmutableList<LogicVariable>) params[3];
            boolean nullable = (Boolean) params[4];
            KeYJavaType resultType = (KeYJavaType) params[5];
            if (resultType == null) {
                // quick fix. may happen with \num_of
                resultType = services.getTypeConverter().getKeYJavaType(PrimitiveType.JAVA_BIGINT);
            }

            for (LogicVariable lv : declVars) {
                preTerm = tb.and(preTerm,
                                 tb.reachableValue(tb.var(lv), declsType));
                if (lv.sort().extendsTrans(services.getJavaInfo().objectSort())
                    && !nullable) {
                    final Term nonNull = arrayDepth > 0 ?
                            tb.deepNonNull(tb.var(lv), tb.zTerm(arrayDepth))
                            : tb.not(tb.equals(tb.var(lv), tb.NULL()));
                    preTerm = tb.and(preTerm, nonNull);
                }
            }

            final SLExpression res = isGeneralized()? translateGeneralizedQuantifiers(declsType,nullable,declVars,preTerm,bodyTerm, resultType)
                    :translateQuantifiers(declVars, preTerm, bodyTerm);
            return res;
        }


        public SLExpression translateQuantifiers(Iterable<LogicVariable> qvs,
                                         Term t1,
                                         Term t2)
                throws SLTranslationException {
            t2 = tb.convertToFormula(t2);
            Term result = combineQuantifiedTerms(t1, t2);
            for (LogicVariable qv : qvs) {
                result = translateQuantifier(qv, result);
            }
            return new SLExpression(result);
        }

        public SLExpression translateGeneralizedQuantifiers(KeYJavaType declsType, boolean nullable, Iterable<LogicVariable> qvs, Term t1, Term t2, KeYJavaType resultType)
        throws SLTranslationException {
            Iterator<LogicVariable> it = qvs.iterator();
            LogicVariable qv = it.next();
            assert resultType != null;
            if (it.hasNext()) {
                throw new SLTranslationException("Only one quantified variable is allowed in this context.");
            }
            Term cond = tb.convertToBoolean(tb.and(t1, t2));
            return new SLExpression(translateQuantifier(qv, cond),resultType);
        }
        
        /** Provide restriction terms for the declared KeYJavaType */
        protected Term typerestrict(KeYJavaType kjt, final boolean nullable, Iterable<QuantifiableVariable> qvs, Services services) {
            final Type type = kjt.getJavaType();
            final int arrayDepth = JMLSpecExtractor.arrayDepth(type, services);
            Term res = tb.tt();
            for (QuantifiableVariable qv: qvs) {
                if (type instanceof PrimitiveType) {
                    if (type == PrimitiveType.JAVA_BYTE) res = tb.and(res,tb.inByte(tb.var(qv)));
                    if (type == PrimitiveType.JAVA_SHORT) res = tb.and(res,tb.inShort(tb.var(qv)));
                    if (type == PrimitiveType.JAVA_CHAR) res = tb.and(res,tb.inChar(tb.var(qv)));
                    if (type == PrimitiveType.JAVA_INT) res = tb.and(res,tb.inInt(tb.var(qv)));
                    if (type == PrimitiveType.JAVA_LONG) res = tb.and(res,tb.inLong(tb.var(qv)));
                } else {
                    // assume reference type
                    if (nullable) {
                        res = tb.and(res,tb.created(tb.var(qv)));
                    } else {
                        final Term nonNull = arrayDepth > 0 ?
                                tb.deepNonNull(tb.var(qv), tb.zTerm(arrayDepth))
                                : tb.not(tb.equals(tb.var(qv), tb.NULL()));
                        res = tb.and(res,tb.and(
                                tb.created(tb.var(qv)), nonNull));
                    }
                }
            }
            return res;
        }

        public abstract Term combineQuantifiedTerms(Term t1,
                                                    Term t2)
                throws SLTranslationException;


        public abstract Term translateQuantifier(QuantifiableVariable qv,
                                                 Term t)
                throws SLTranslationException;

        protected abstract boolean isGeneralized ();
    }

    /**
     * Abstract super-class for translation methods which enumerate fields such as <code>\reach</code>.
     * @author bruns
     *
     */
    private abstract class JMLFieldAccessExpressionTranslationMethod implements JMLTranslationMethod {

        /**
         * Creates an "all-objects" term from a store-ref term.
         * @param t store-ref term, needs to be a union of singletons
         * @param services
         * @return allObjects term (see <code>LocSetADT</code>)
         * @throws SLTranslationException in case <code>t</code> is not a store-ref term cosisting of unions of singletons
         */
        protected Term getFields(SLTranslationExceptionManager excManager, Term t, Services services) throws SLTranslationException {
            final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
            if(t.op().equals(locSetLDT.getUnion())) {
                final Term sub0 = getFields(excManager, t.sub(0),services);
                final Term sub1 = getFields(excManager, t.sub(1),services);
                return tb.union(sub0, sub1);
            } else if(t.op().equals(locSetLDT.getSingleton())) {
            return tb.allObjects(t.sub(1));
            } else {
                throw excManager.createException("Inacceptable field expression: " + t);
            }
        }
    }

    private abstract class JMLBoundedNumericalQuantifierTranslationMethod extends JMLQuantifierTranslationMethod {

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


        @SuppressWarnings("unchecked")
        @Override
        public SLExpression translate(SLTranslationExceptionManager excManager, Object... params)
                throws SLTranslationException {
            checkParameters(params,
                    Term.class, Term.class, KeYJavaType.class,
                    ImmutableList.class, Boolean.class, KeYJavaType.class, Services.class);
            final KeYJavaType _declsType = (KeYJavaType) params[2];
            de.uka.ilkd.key.java.abstraction.Type declsType =
                    _declsType.getJavaType();
            ImmutableList<QuantifiableVariable> qvs = (ImmutableList)params[3];
            boolean nullable = (Boolean) params[4];
            services = (Services) params[6];
            assert services != null;
            KeYJavaType resultType = (KeYJavaType) params[5];
            if (resultType == null) // happens with num_of
                resultType = services.getTypeConverter().getKeYJavaType(PrimitiveType.JAVA_BIGINT);

            if (declsType instanceof PrimitiveType && ((PrimitiveType)declsType).isIntegerType())
                return super.translate(excManager, params);
            else
                return new SLExpression(
                        translateUnboundedNumericalQuantifier(_declsType, nullable, qvs,
                                                              (Term)params[0], (Term)params[1]),
                        resultType);
        }

        @Override
        @Deprecated
        public SLExpression translateQuantifiers(Iterable<LogicVariable> qvs, Term t1, Term t2) {
            assert false;
            return null;
        }

        @Override
        public SLExpression translateGeneralizedQuantifiers(KeYJavaType declsType, boolean nullable, Iterable<LogicVariable> qvs,
                Term t1,
                Term t2, KeYJavaType resultType)
                        throws SLTranslationException {
            Iterator<LogicVariable> it = qvs.iterator();
            LogicVariable lv = it.next();
            Term t;
            if (it.hasNext() || !isBoundedNumerical(t1, lv)) {
                // not interval range, create unbounded comprehension term
                ImmutableList<QuantifiableVariable> _qvs = ImmutableSLList.<QuantifiableVariable>nil().prepend(lv);
                while (it.hasNext()) _qvs = _qvs.prepend(it.next());
                t = translateUnboundedNumericalQuantifier(declsType, nullable, _qvs, t1, t2);
            } else {
                t = translateBoundedNumericalQuantifier(lv,
                        lowerBound(t1, lv),
                        upperBound(t1, lv),
                        t2);
            }
            final JavaIntegerSemanticsHelper jish = new JavaIntegerSemanticsHelper(services, excManager);
            // cast to specific JML type (fixes bug #1347)
            return jish.buildCastExpression(resultType, new SLExpression(t, resultType));
        }

        protected abstract Term translateUnboundedNumericalQuantifier(KeYJavaType declsType, boolean nullable, ImmutableList<QuantifiableVariable> qvs, Term range, Term body);

        @Override
        protected boolean isGeneralized () {
            return true;
        }

        /** Creates a term for a bounded numerical quantifier (e.g., sum).*/
        public abstract Term translateBoundedNumericalQuantifier(QuantifiableVariable qv, Term lo, Term hi, Term body);


        /** Should not be called. */
        @Override
        @Deprecated
        public Term combineQuantifiedTerms(Term t1,
                Term t2) {
            assert false;
            return null;
        }


        /** Should not be called. */
        @Override
        @Deprecated
        public Term translateQuantifier(QuantifiableVariable qv,
                Term t) {
            assert false;
            return null;
        }
    }
    
    private abstract class JMLEqualityTranslationMethod implements
            JMLTranslationMethod {

        protected void checkSLExpressions(SLExpression expr1,
                                          SLExpression expr2,
                                          SLTranslationExceptionManager excManager,
                                          String eqSymb)
        throws SLTranslationException {
            if (expr1.isType() != expr2.isType()) {
                throw excManager.createException(
                        "Cannot build equality expression (" + eqSymb
                        + ") between term and type.\n" +
                        		"The expression was: "+expr1+eqSymb+expr2);
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
                        throw excManager.createException(
                                "Type equality only supported for expressions "
                                + " of shape \"\\typeof(term) == \\type(Typename)\"");
                    }
                    typeofExpr = b;
                    typeExpr = a;
                }

                Sort os = typeExpr.getType().getSort();
                Function ioFunc = os.getExactInstanceofSymbol(services);

                return new SLExpression(tb.equals(
                        tb.func(ioFunc, typeofExpr.getTerm()),
                        tb.TRUE()));
            }

            // this should not be reached
            throw excManager.createException("Equality must be between two terms or " +
            		"two formulas, not term and formula.");
        }


        protected Term buildEqualityTerm(Term a,
                                         Term b,
                                         SLTranslationExceptionManager excManager1,
                                         Services services)
                throws SLTranslationException {

            Term result = null;
            try {
                if (a.sort() != Sort.FORMULA && b.sort() != Sort.FORMULA) {
                    result = tb.equals(a, b);
                // Special case so that model methods are handled better
                } else if(a.sort() == services.getTypeConverter().getBooleanLDT().targetSort() && b.sort() == Sort.FORMULA) {
                    result = tb.equals(a, tb.ife(b, tb.TRUE(), tb.FALSE()));
                } else {
                    result = tb.equals(tb.convertToFormula(a),
                                       tb.convertToFormula(b));
                }
                return result;
            } catch (IllegalArgumentException e) {
                throw excManager1.createException(
                        "Illegal Arguments in equality expression.");
                //"near " + LT(0));
            } catch (TermCreationException e) {
                throw excManager1.createException("Error in equality-expression\n"
                                           + a.toString() + " == "
                                           + b.toString() + ".");
            }
        }
    }

    /**
     * Translation methods for (binary) arithmetic operations.
     * Contains checks whether \bigint or Java integer semantics should be used.
     * @author bruns
     *
     */
    private abstract class JMLArithmeticOperationTranslationMethod implements JMLTranslationMethod {

        protected KeYJavaType bigint;

        protected String BIGINT_NOT_ALLOWED = "Operation "+opName()+" may only be used with primitive Java types, not with \\bigint";

        protected boolean isBigint(SLExpression e) {
            assert bigint != null;
            return e.getType().equals(bigint);
        }

        protected void checkNotBigint(SLExpression e) throws SLTranslationException {
            if (isBigint(e)) {
                throw new SLTranslationException(BIGINT_NOT_ALLOWED);
            }
        }

        private void checkNotType(SLExpression e, SLTranslationExceptionManager man)
                throws SLTranslationException {
            if (e.isType()) {
                throw man.createException("Cannot use operation "+opName()+" on type " +
                        e.getType().getName() + ".");
            }
            assert e.isTerm();
        }

        @Override
        public SLExpression translate (SLTranslationExceptionManager man, Object ... params ) throws SLTranslationException{
            checkParameters(params, Services.class, SLExpression.class, SLExpression.class);
            JavaIntegerSemanticsHelper jish = new JavaIntegerSemanticsHelper((Services)params[0],man);
            bigint = ((Services)params[0]).getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BIGINT);
            SLExpression e1 = (SLExpression) params[1];
            SLExpression e2 = (SLExpression) params[2];
            checkNotType(e1,man);
            checkNotType(e2,man);
            SLExpression result = null;
            try {
                result = translate(jish,e1,e2);
            } catch (SLTranslationException cause){
                throw man.createException("Cannot create JML arithmetic expression", cause);
            }
            return result;
        }

        protected abstract String opName();
        protected abstract SLExpression translate(JavaIntegerSemanticsHelper intHelper, SLExpression left, SLExpression right) throws SLTranslationException;
    }
}