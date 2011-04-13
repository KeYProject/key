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
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;



/**
 * Translates JML expressions to FOL.
 */
final class JMLTranslator {

    private final static JMLTranslator instance = new JMLTranslator();
    private final static TermBuilder TB = TermBuilder.DF;

    private LinkedHashMap<String, JMLTranslationMethod> translationMethods;


    private abstract class JMLQuantifierTranslationMethod implements
            JMLTranslationMethod {

        /**
         * Add implicit "non-null" and "created" guards for reference types,
         * "in-bounds" guards for integer types. Then, translate the quantifier.
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
        @Override
        public Term translate(Object... params)
                throws SLTranslationException {
            Pair<KeYJavaType, ImmutableList<LogicVariable>> declVars =
                    (Pair<KeYJavaType, ImmutableList<LogicVariable>>) params[0];
            Term preTerm = (Term) params[1];
            Term bodyTerm = (Term) params[2];
            boolean nullable = (Boolean) params[3];
            Services services = (Services) params[4];
            Term nullTerm = TB.NULL(services);
            for (LogicVariable lv : declVars.second) {
                preTerm = TB.and(preTerm,
                                 TB.reachableValue(services, TB.var(lv),
                                                   declVars.first));
                if (lv.sort().extendsTrans(services.getJavaInfo().objectSort())
                    && !nullable) {
                    preTerm = TB.and(preTerm, TB.not(TB.equals(TB.var(lv),
                                                               nullTerm)));
                }
            }

            return translateQuantifiers(declVars.second, preTerm, bodyTerm);
        }


        public Term translateQuantifiers(Iterable<LogicVariable> qvs,
                                         Term t1,
                                         Term t2)
                throws SLTranslationException {
            if (!qvs.iterator().hasNext()) {
                throw new TermCreationException(
                        "Cannot quantify over 0 variables");
            }
            Term result = t2;
            for (LogicVariable qv : qvs) {
                result = translateQuantifier(qv, t1, result);
            }
            return result;
        }

        public abstract Term translateQuantifier(QuantifiableVariable qv,
                                                 Term t1,
                                                 Term t2)
                throws SLTranslationException;
    }


    private JMLTranslator() {
        translationMethods = new LinkedHashMap<String, JMLTranslationMethod>();

        // quantifiers
        translationMethods.put("\\forall", new JMLQuantifierTranslationMethod() {
            @Override
            public Term translateQuantifier(QuantifiableVariable qv,
                                            Term t1,
                                            Term t2)
                    throws SLTranslationException {
                return TB.all(qv, TB.imp(t1, t2));
            }
        });
        translationMethods.put("\\exists", new JMLQuantifierTranslationMethod() {
            @Override
            public Term translateQuantifier(QuantifiableVariable qv,
                                            Term t1,
                                            Term t2)
                    throws SLTranslationException {
                return TB.ex(qv, TB.and(t1, t2));
            }
        });
//        translationMethods.put("\\min", new Name("min"));
//        translationMethods.put("\\max", new Name("max"));
//        translationMethods.put("\\num_of", new Name("num_of"));
//        translationMethods.put("\\product", new Name("product"));
//        translationMethods.put("\\sum", new Name("bsum"));

    }


    public static JMLTranslator getInstance() {
        return instance;
    }


    //-------------------------------------------------------------------------


    public Term translate(String jmlKeyword,
                          Object... params)
            throws SLTranslationException {
        JMLTranslationMethod m = translationMethods.get(jmlKeyword);
        if (m != null) {
            return m.translate(params);
        } else {
            throw new SLTranslationException(
                    "Unknown translation for JML-keyword \""
                    + jmlKeyword
                    + "\". The keyword seems not to be supported jet.");
        }
    }



    /**
     * Translates a normal top-level JML expression, i.e. a formula.
     */
    public Term translateExpression(PositionedString expr,
                                    KeYJavaType specInClass,
                                    ProgramVariable selfVar,
                                    ImmutableList<ProgramVariable> paramVars,
                                    ProgramVariable resultVar,
                                    ProgramVariable excVar,
                                    Term heapAtPre,
                                    Services services)
            throws SLTranslationException {
        assert expr != null;
        assert specInClass != null;

        final KeYJMLParser parser = new KeYJMLParser(expr,
                                                     services,
                                                     specInClass,
                                                     selfVar,
                                                     paramVars,
                                                     resultVar,
                                                     excVar,
                                                     heapAtPre);

        final Term result = parser.parseExpression();
        return result;
    }


    /**
     * Translates an expression as it occurs in JML signals-clauses, 
     * i.e. something of the form
     *       "(typename) expression"
     * or
     *       "(typename varname) expression"
     */
    public Term translateSignalsExpression(
            PositionedString signalsExpr,
            KeYJavaType specInClass,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            ProgramVariable resultVar,
            ProgramVariable excVar,
            Term heapAtPre,
            Services services)
            throws SLTranslationException {

        final KeYJMLParser parser = new KeYJMLParser(signalsExpr,
                                                     services,
                                                     specInClass,
                                                     selfVar,
                                                     paramVars,
                                                     resultVar,
                                                     excVar,
                                                     heapAtPre);
        final Term result = parser.parseSignals();
        return result;
    }


    /**
     * Translates an expression as it occurs in JML signals_only-clauses,
     * i.e. a list of types.
     */
    public Term translateSignalsOnlyExpression(
            PositionedString signalsOnlyExpr,
            KeYJavaType specInClass,
            ProgramVariable excVar,
            Services services)
            throws SLTranslationException {

        final KeYJMLParser parser = new KeYJMLParser(signalsOnlyExpr,
                                                     services,
                                                     specInClass,
                                                     null,
                                                     null,
                                                     null,
                                                     excVar,
                                                     null);

        final Term result = parser.parseSignalsOnly();
        return result;
    }


    /**
     * Translates an expression as it occurs in JML assignable-clauses.
     */
    public Term translateAssignableExpression(
            PositionedString assignableExpr,
            KeYJavaType specInClass,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Services services)
            throws SLTranslationException {

        final KeYJMLParser parser = new KeYJMLParser(assignableExpr,
                                                     services,
                                                     specInClass,
                                                     selfVar,
                                                     paramVars,
                                                     null,
                                                     null,
                                                     null);

        final Term result = parser.parseAssignable();
        return result;
    }


    public ImmutableList<Term> translateSecureForExpression(
            PositionedString assignableExpr,
            KeYJavaType specInClass,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Services services)
            throws SLTranslationException {

        final KeYJMLParser parser = new KeYJMLParser(assignableExpr,
                                                     services,
                                                     specInClass,
                                                     selfVar,
                                                     paramVars,
                                                     null,
                                                     null,
                                                     null);

        final ImmutableList<Term> result = parser.parseSecureFor();
        return result;
    }


    public ImmutableList<Term> translateDeclassifyExpression(
            PositionedString assignableExpr,
            KeYJavaType specInClass,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Services services)
            throws SLTranslationException {

        final KeYJMLParser parser = new KeYJMLParser(assignableExpr,
                                                     services,
                                                     specInClass,
                                                     selfVar,
                                                     paramVars,
                                                     null,
                                                     null,
                                                     null);

        final ImmutableList<Term> result = parser.parseDeclassify();
        return result;
    }


    public ImmutableList<Term> translateDeclassifyVarExpression(
            PositionedString assignableExpr,
            KeYJavaType specInClass,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Services services)
            throws SLTranslationException {

        final KeYJMLParser parser = new KeYJMLParser(assignableExpr,
                                                     services,
                                                     specInClass,
                                                     selfVar,
                                                     paramVars,
                                                     null,
                                                     null,
                                                     null);

        final ImmutableList<Term> result = parser.parseDeclassifyVar();
        return result;
    }


    /**
     * Translates an expression as it occurs in JML represents-clauses.
     */
    public Pair<ObserverFunction, Term> translateRepresentsExpression(
            PositionedString representsExpr,
            KeYJavaType specInClass,
            ProgramVariable selfVar,
            Services services)
            throws SLTranslationException {

        final KeYJMLParser parser = new KeYJMLParser(representsExpr,
                                                     services,
                                                     specInClass,
                                                     selfVar,
                                                     null,
                                                     null,
                                                     null,
                                                     null);

        final Pair<ObserverFunction, Term> result = parser.parseRepresents();
        return result;
    }


    /**
     * Translates an expression as it occurs in our custom class-level accessible clauses.
     */
    public Triple<ObserverFunction, Term, Term> translateDependsExpression(
            PositionedString accessibleExpr,
            KeYJavaType specInClass,
            ProgramVariable selfVar,
            Services services)
            throws SLTranslationException {

        final KeYJMLParser parser = new KeYJMLParser(accessibleExpr,
                                                     services,
                                                     specInClass,
                                                     selfVar,
                                                     null,
                                                     null,
                                                     null,
                                                     null);

        final Triple<ObserverFunction, Term, Term> result =
                parser.parseDepends();
        return result;
    }


    public ImmutableList<ProgramVariable> translateVariableDeclaration(
            PositionedString variableDecl,
            Services services)
            throws SLTranslationException {
        final KeYJMLParser parser = new KeYJMLParser(variableDecl,
                                                     services,
                                                     null,
                                                     null,
                                                     null,
                                                     null,
                                                     null,
                                                     null);

        final ImmutableList<ProgramVariable> result =
                parser.parseVariableDeclaration();
        return result;
    }
}
