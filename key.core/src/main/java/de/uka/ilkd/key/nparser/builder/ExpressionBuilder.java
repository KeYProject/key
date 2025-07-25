/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.builder;

import java.math.BigInteger;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Objects;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.ldt.*;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.nparser.KeYLexer;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.KeYParser.DoubleLiteralContext;
import de.uka.ilkd.key.nparser.KeYParser.FloatLiteralContext;
import de.uka.ilkd.key.nparser.KeYParser.RealLiteralContext;
import de.uka.ilkd.key.parser.NotDeclException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.parsing.BuildingException;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.TermCreationException;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.ParsableVariable;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.StringUtil;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This visitor creates expression from {@link de.uka.ilkd.key.nparser.KeyAst.Term}. You should use
 * the facade {@link de.uka.ilkd.key.nparser.KeyIO#parseExpression(String)} for term parsing.
 *
 * @author weigl
 */
public class ExpressionBuilder extends DefaultBuilder {
    public static final Logger LOGGER = LoggerFactory.getLogger(ExpressionBuilder.class);

    public static final String NO_HEAP_EXPRESSION_BEFORE_AT_EXCEPTION_MESSAGE =
        "Expecting select term before '@', not: ";

    /**
     * The current abbreviation used for resolving "@name" terms.
     */
    private AbbrevMap abbrevMap;

    /**
     * Altlast.
     */
    private JTerm quantifiedArrayGuard;

    /**
     * A list of terms, that are marked for having an already set heap.
     */
    private final List<JTerm> explicitHeap = new LinkedList<>();

    /**
     *
     */
    protected boolean javaSchemaModeAllowed = false;

    public ExpressionBuilder(Services services, NamespaceSet nss) {
        this(services, nss, new Namespace<>());
    }

    public ExpressionBuilder(Services services, NamespaceSet nss,
            Namespace<SchemaVariable> schemaNamespace) {
        super(services, nss);
        setSchemaVariables(schemaNamespace);
    }

    public static JTerm updateOrigin(JTerm t, ParserRuleContext ctx, Services services) {
        try {
            t = services.getTermFactory().createTermWithOrigin(t,
                ctx.start.getTokenSource().getSourceName() + "@" + ctx.start.getLine()
                    + ":" + ctx.start.getCharPositionInLine() + 1);
        } catch (ClassCastException ignored) {
        }
        return t;
    }

    /**
     * Given a raw modality string, this function trims the modality information.
     *
     * @param raw non-null string
     * @return non-null string
     */
    public static String trimJavaBlock(String raw) {
        if (raw.startsWith("\\<")) {
            return StringUtil.trim(raw, "\\<>");
        }
        if (raw.startsWith("\\[")) {
            return StringUtil.trim(raw, "\\[]");
        }
        int end = raw.length() - (raw.endsWith("\\endmodality") ? "\\endmodality".length() : 0);
        int start = 0;
        if (raw.startsWith("\\throughout_transaction")) {
            start = "\\throughout_transaction".length();
        } else if (raw.startsWith("\\diamond_transaction")) {
            start = "\\diamond_transaction".length();
        } else if (raw.startsWith("\\diamond")) {
            start = "\\diamond".length();
        } else if (raw.startsWith("\\box_transaction")) {
            start = "\\box_transaction".length();
        } else if (raw.startsWith("\\box")) {
            start = "\\box".length();
        } else if (raw.startsWith("\\throughout")) {
            start = "\\throughout".length();
        } else if (raw.startsWith("\\modality")) {
            start = raw.indexOf('}') + 1;
        }
        return raw.substring(start, end);
    }

    /**
     * Given a raw modality string, this method determines the operator name.
     */
    public static String operatorOfJavaBlock(String raw) {
        if (raw.startsWith("\\<")) {
            return "diamond";
        }
        if (raw.startsWith("\\[")) {
            return "box";
        }
        if (raw.startsWith("\\diamond_transaction")) {
            return "diamond_transaction";
        }
        if (raw.startsWith("\\box_transaction")) {
            return "box_transaction";
        }
        if (raw.startsWith("\\diamond")) {
            return "diamond";
        }
        if (raw.startsWith("\\box")) {
            return "box";
        }
        if (raw.startsWith("\\throughout_transaction")) {
            return "throughout_transaction";
        }
        if (raw.startsWith("\\throughout")) {
            return "throughout";
        }
        if (raw.startsWith("\\modality")) {
            int start = raw.indexOf('{') + 1;
            int end = raw.indexOf('}');
            return raw.substring(start, end);
        }
        return "n/a";
    }

    private static boolean isSelectTerm(JTerm term) {
        return term.op().name().toString().endsWith("::select") && term.arity() == 3;
    }

    @Override
    public JTerm visitParallel_term(KeYParser.Parallel_termContext ctx) {
        List<JTerm> t = mapOf(ctx.elementary_update_term());
        JTerm a = t.get(0);
        for (int i = 1; i < t.size(); i++) {
            a = getTermFactory().createTerm(UpdateJunctor.PARALLEL_UPDATE, a, t.get(i));
        }
        return updateOrigin(a, ctx, services);
    }

    @Override
    public JTerm visitTermEOF(KeYParser.TermEOFContext ctx) {
        return accept(ctx.term());
    }

    @Override
    public JTerm visitElementary_update_term(KeYParser.Elementary_update_termContext ctx) {
        JTerm a = accept(ctx.a);
        JTerm b = accept(ctx.b);
        if (b != null) {
            return updateOrigin(getServices().getTermBuilder().elementary(a, b), ctx, services);
        }
        return updateOrigin(a, ctx, services);
    }

    @Override
    public JTerm visitEquivalence_term(KeYParser.Equivalence_termContext ctx) {
        JTerm a = accept(ctx.a);
        if (ctx.b.isEmpty()) {
            return a;
        }

        JTerm cur = a;
        for (KeYParser.Implication_termContext context : ctx.b) {
            JTerm b = accept(context);
            cur = binaryTerm(ctx, Equality.EQV, cur, b);

        }
        return cur;
    }

    private JTerm binaryTerm(ParserRuleContext ctx, Operator operator,
            JTerm left, JTerm right) {
        if (right == null) {
            return updateOrigin(left, ctx, services);
        }
        return capsulateTf(ctx,
            () -> updateOrigin(getTermFactory().createTerm(operator, left, right), ctx,
                services));
    }

    @Override
    public JTerm visitImplication_term(KeYParser.Implication_termContext ctx) {
        JTerm termL = accept(ctx.a);
        JTerm termR = accept(ctx.b);
        return binaryTerm(ctx, Junctor.IMP, termL, termR);
    }

    @Override
    public JTerm visitDisjunction_term(KeYParser.Disjunction_termContext ctx) {
        JTerm t = accept(ctx.a);
        for (KeYParser.Conjunction_termContext c : ctx.b) {
            t = binaryTerm(ctx, Junctor.OR, t, accept(c));
        }
        return t;
    }

    @Override
    public JTerm visitConjunction_term(KeYParser.Conjunction_termContext ctx) {
        JTerm t = accept(ctx.a);
        for (KeYParser.Term60Context c : ctx.b) {
            t = binaryTerm(ctx, Junctor.AND, t, accept(c));
        }
        return t;
        // Term termR = accept(ctx.b);
        // return binaryTerm(ctx, Junctor.AND, termL, termR);
    }

    @Override
    public Object visitUnary_minus_term(KeYParser.Unary_minus_termContext ctx) {
        JTerm result = accept(ctx.sub);
        assert result != null;
        if (ctx.MINUS() != null) {
            Function Z = functions().lookup("Z");
            if (result.op() == Z) {
                // weigl: rewrite neg(Z(1(#)) to Z(neglit(1(#))
                // This mimics the old KeyParser behaviour. Unknown if necessary.
                final Function neglit = functions().lookup("neglit");
                final JTerm num = result.sub(0);
                return capsulateTf(ctx,
                    () -> getTermFactory().createTerm(Z, getTermFactory().createTerm(neglit, num)));
            } else if (result.sort() != JavaDLTheory.FORMULA) {
                Sort sort = result.sort();
                if (sort == null) {
                    semanticError(ctx, "No sort for %s", result);
                }
                LDT ldt = services.getTypeConverter().getLDTFor(sort);
                if (ldt == null) {
                    // falling back to integer ldt (for instance for untyped schema variables)
                    ldt = services.getTypeConverter().getIntegerLDT();
                }
                Function op = ldt.getFunctionFor("neg", services);
                if (op == null) {
                    semanticError(ctx, "Could not find function symbol 'neg' for sort '%s'.", sort);
                }
                return capsulateTf(ctx, () -> getTermFactory().createTerm(op, result));
            } else {
                semanticError(ctx, "Formulas cannot be prefixed with '-'");
            }
        }
        return result;
    }

    @Override
    public JTerm visitNegation_term(KeYParser.Negation_termContext ctx) {
        JTerm termL = accept(ctx.sub);
        if (ctx.NOT() != null) {
            return capsulateTf(ctx, () -> getTermFactory().createTerm(Junctor.NOT, termL));
        } else {
            return termL;
        }
    }

    @Override
    public JTerm visitEquality_term(KeYParser.Equality_termContext ctx) {
        JTerm termL = accept(ctx.a);
        JTerm termR = accept(ctx.b);
        JTerm eq = binaryTerm(ctx, Equality.EQUALS, termL, termR);
        if (ctx.NOT_EQUALS() != null) {
            return capsulateTf(ctx, () -> getTermFactory().createTerm(Junctor.NOT, eq));
        }
        return eq;
    }

    @Override
    public Object visitComparison_term(KeYParser.Comparison_termContext ctx) {
        JTerm termL = accept(ctx.a);
        JTerm termR = accept(ctx.b);

        if (termR == null) {
            return updateOrigin(termL, ctx, services);
        }

        String op_name = "";
        if (ctx.LESS() != null) {
            op_name = "lt";
        }
        if (ctx.LESSEQUAL() != null) {
            op_name = "leq";
        }
        if (ctx.GREATER() != null) {
            op_name = "gt";
        }
        if (ctx.GREATEREQUAL() != null) {
            op_name = "geq";
        }
        return binaryLDTSpecificTerm(ctx, op_name, termL, termR);

    }

    @Override
    public Object visitWeak_arith_term(KeYParser.Weak_arith_termContext ctx) {
        JTerm termL = Objects.requireNonNull(accept(ctx.a));
        if (ctx.op.isEmpty()) {
            return updateOrigin(termL, ctx, services);
        }

        List<JTerm> terms = mapOf(ctx.b);
        JTerm last = termL;
        for (int i = 0; i < terms.size(); i++) {
            String opname = "";
            switch (ctx.op.get(i).getType()) {
                case KeYLexer.UTF_INTERSECT -> opname = LocSetLDT.INTERSECT_STRING;
                case KeYLexer.UTF_SETMINUS -> opname = LocSetLDT.SETMINUS_STRING;
                case KeYLexer.UTF_UNION -> opname = LocSetLDT.UNION_STRING;
                case KeYLexer.PLUS -> opname = IntegerLDT.ADD_STRING;
                case KeYLexer.MINUS -> opname = IntegerLDT.SUB_STRING;
                default -> semanticError(ctx, "Unexpected token: %s", ctx.op.get(i));
            }
            JTerm cur = terms.get(i);
            last = binaryLDTSpecificTerm(ctx, opname, last, cur);
        }
        return last;
    }

    private JTerm binaryLDTSpecificTerm(ParserRuleContext ctx, String opname, JTerm last,
            JTerm cur) {
        Sort sort = last.sort();
        if (sort == null) {
            semanticError(ctx, "No sort for %s", last);
        }
        LDT ldt = services.getTypeConverter().getLDTFor(sort);
        if (ldt == null) {
            // falling back to integer ldt (for instance for untyped schema variables)
            ldt = services.getTypeConverter().getIntegerLDT();
        }
        Function op = ldt.getFunctionFor(opname, services);
        if (op == null) {
            semanticError(ctx, "Could not find function symbol '%s' for sort '%s'.", opname, sort);
        }
        return binaryTerm(ctx, op, last, cur);
    }


    @Override
    public Object visitStrong_arith_term_1(KeYParser.Strong_arith_term_1Context ctx) {
        JTerm termL = accept(ctx.a);
        if (ctx.b.isEmpty()) {
            return updateOrigin(termL, ctx, services);
        }
        List<JTerm> terms = mapOf(ctx.b);
        JTerm last = termL;
        for (JTerm cur : terms) {
            last = binaryLDTSpecificTerm(ctx, IntegerLDT.MUL_STRING, last, cur);
        }
        return last;
    }

    @Override
    public Object visitEmptyset(KeYParser.EmptysetContext ctx) {
        var op = services.getTypeConverter().getLocSetLDT().getEmpty();
        return updateOrigin(getTermFactory().createTerm(op), ctx, services);
    }

    @Override
    public Object visitStrong_arith_term_2(KeYParser.Strong_arith_term_2Context ctx) {
        if (ctx.b.isEmpty()) { // fast path
            return accept(ctx.a);
        }

        List<JTerm> termL = mapOf(ctx.b);
        // List<String> opName = ctx.op.stream().map(it -> it.getType()== KeYLexer.PERCENT ? "mod" :
        // "div").collect(Collectors.toList());

        JTerm term = accept(ctx.a);
        var sort = term.sort();
        if (sort == null) {
            semanticError(ctx, "No sort for term '%s'", term);
        }

        var ldt = services.getTypeConverter().getLDTFor(sort);

        if (ldt == null) {
            // falling back to integer ldt (for instance for untyped schema variables)
            ldt = services.getTypeConverter().getIntegerLDT();
        }

        assert ctx.op.size() == ctx.b.size();

        for (int i = 0; i < termL.size(); i++) {
            var opName = ctx.op.get(i).getType() == KeYLexer.PERCENT ? "mod" : "div";
            Function op = ldt.getFunctionFor(opName, services);
            if (op == null) {
                semanticError(ctx, "Could not find function symbol '%s' for sort '%s'.", opName,
                    sort);
            }
            term = binaryTerm(ctx, op, term, termL.get(i));
        }
        return term;
    }

    protected JTerm capsulateTf(ParserRuleContext ctx, Supplier<JTerm> termSupplier) {
        try {
            return termSupplier.get();
        } catch (TermCreationException e) {
            throw new BuildingException(ctx,
                String.format("Could not build term on: %s", ctx.getText()), e);
        }
    }

    @Override
    public Object visitBracket_term(KeYParser.Bracket_termContext ctx) {
        JTerm t = accept(ctx.primitive_labeled_term());
        for (int i = 0; i < ctx.bracket_suffix_heap().size(); i++) {
            KeYParser.Brace_suffixContext brace_suffix = ctx.bracket_suffix_heap(i).brace_suffix();
            ParserRuleContext heap = ctx.bracket_suffix_heap(i).heap;
            t = accept(brace_suffix, t);
            if (heap != null) {
                t = replaceHeap(t, accept(heap), heap);
            }
        }
        if (ctx.attribute().isEmpty()) {
            return t;
        }
        return handleAttributes(t, ctx.attribute());
    }

    /*
     * @Override public String
     * visitStaticAttributeOrQueryReference(KeYParser.StaticAttributeOrQueryReferenceContext ctx) {
     * //TODO weigl: this rule is a total grammar blower. String attrReference = ctx.id.getText();
     * for (int i = 0; i < ctx.EMPTYBRACKETS().size(); i++) { attrReference += "[]"; }
     *
     * /*KeYJavaType kjt = null; kjt = getTypeByClassName(attrReference); if (kjt == null) {
     * throwEx(new NotDeclException(input, "Class", attrReference)); } attrReference =
     * kjt.getSort().name().toString(); match(input, DOT, null); attrReference += "::" +
     * input.LT(1).getText(); match(input, IDENT, null); if(savedGuessing > -1) { state.backtracking
     * = savedGuessing; savedGuessing = -1; }
     */
    // return attrReference;
    // }

    /*
     * @Override public Term visitStatic_attribute_suffix(KeYParser.Static_attribute_suffixContext
     * ctx) { Operator v = null; String attributeName =
     * accept(ctx.staticAttributeOrQueryReference()); String className; if
     * (attributeName.indexOf(':') != -1) { className = attributeName.substring(0,
     * attributeName.indexOf(':')); } else { className = attributeName.substring(0,
     * attributeName.lastIndexOf(".")); } v =
     * getAttributeInPrefixSort(getTypeByClassName(className).getSort(), attributeName); return
     * createAttributeTerm(null, v, ctx); }
     */

    private LogicVariable bindVar(String id, Sort s) {
        LogicVariable v = new LogicVariable(new Name(id), s);
        namespaces().setVariables(variables().extended(v));
        return v;
    }

    private LogicVariable bindVar(LogicVariable v) {
        namespaces().setVariables(variables().extended(v));
        return v;
    }

    private void bindVar() {
        namespaces().setVariables(new Namespace<>(variables()));
    }

    private JTerm toZNotation(String literal, Namespace<Function> functions) {
        literal = literal.replace("_", "");
        final boolean negative = (literal.charAt(0) == '-');
        if (negative) {
            literal = literal.substring(1);
        }
        int base = 10;

        if (literal.startsWith("0x")) {
            literal = literal.substring(2);
            base = 16;
        }

        if (literal.startsWith("0b")) {
            literal = literal.substring(2);
            base = 8;
        }

        BigInteger bi = new BigInteger(literal, base);
        return toZNotation(bi, functions);
    }

    private JTerm toZNotation(BigInteger bi, Namespace<Function> functions) {
        boolean negative = bi.signum() < 0;
        String s = bi.abs().toString();
        JTerm result = getTermFactory().createTerm(functions.lookup(new Name("#")));

        for (int i = 0; i < s.length(); i++) {
            result = getTermFactory().createTerm(
                functions.lookup(new Name(s.substring(i, i + 1))),
                result);
        }

        if (negative) {
            result = getTermFactory().createTerm(functions.lookup(new Name("neglit")),
                result);
        }
        return getTermFactory().createTerm(functions.lookup(new Name("Z")), result);
    }

    @Override
    public Sequent visitSeq(KeYParser.SeqContext ctx) {
        ImmutableList<SequentFormula> ant = accept(ctx.ant);
        ImmutableList<SequentFormula> suc = accept(ctx.suc);
        return JavaDLSequentKit.createSequent(ant, suc);
    }

    @Override
    public Sequent visitSeqEOF(KeYParser.SeqEOFContext ctx) {
        return accept(ctx.seq());
    }

    @Override
    public Object visitTermorseq(KeYParser.TermorseqContext ctx) {
        JTerm head = accept(ctx.head);
        Sequent s = accept(ctx.s);
        ImmutableList<SequentFormula> ss = accept(ctx.ss);
        if (head != null && s == null && ss == null) {
            return head;
        }
        if (head != null && ss != null) {
            // A sequent with only head in the antecedent.
            var ant = ImmutableSLList.singleton(new SequentFormula(head));
            return JavaDLSequentKit.createSequent(ant, ss);
        }
        if (head != null && s != null) {
            // A sequent. Prepend head to the antecedent.
            var newAnt = s.antecedent().insertFirst(new SequentFormula(head)).getFormulaList();
            return JavaDLSequentKit.createSequent(newAnt, s.succedent().asList());
        }
        if (ss != null) {
            return JavaDLSequentKit.createSequent(ImmutableSLList.nil(), ss);
        }
        assert (false);
        return null;
    }

    @Override
    public ImmutableList<SequentFormula> visitSemisequent(KeYParser.SemisequentContext ctx) {
        ImmutableList<SequentFormula> ss = accept(ctx.ss);
        if (ss == null) {
            ss = ImmutableSLList.nil();
        }
        JTerm head = accept(ctx.term());
        if (head != null) {
            ss = ss.prepend(new SequentFormula(head));
        }
        return ss;
    }

    protected void enableJavaSchemaMode() {
        javaSchemaModeAllowed = true;
    }

    protected void disableJavaSchemaMode() {
        javaSchemaModeAllowed = false;
    }

    private PairOfStringAndJavaBlock getJavaBlock(Token t) {
        PairOfStringAndJavaBlock sjb = new PairOfStringAndJavaBlock();
        String s = t.getText().trim();
        String cleanJava = trimJavaBlock(s);
        sjb.opName = operatorOfJavaBlock(s);

        try {
            try {
                if (javaSchemaModeAllowed) {// TEST
                    SchemaJavaReader jr = new SchemaRecoder2KeY(services, nss);
                    jr.setSVNamespace(schemaVariables());
                    try {
                        sjb.javaBlock =
                            jr.readBlockWithProgramVariables(programVariables(), cleanJava);
                    } catch (Exception e) {
                        sjb.javaBlock = jr.readBlockWithEmptyContext(cleanJava);
                    }
                }
            } catch (Exception e) {
                if (cleanJava.startsWith("{..")) {// do not fallback
                    throw e;
                }
            }

            if (sjb.javaBlock == null) {
                JavaReader jr = new Recoder2KeY(services, nss);
                try {
                    sjb.javaBlock = jr.readBlockWithProgramVariables(programVariables(), cleanJava);
                } catch (Exception e1) {
                    sjb.javaBlock = jr.readBlockWithEmptyContext(cleanJava);
                }
            }
        } catch (ConvertException e) {
            throw new BuildingException(t, "Could not parse java: '" + cleanJava + "'", e);
        }
        return sjb;
    }

    @Override
    public Object visitMetaId(KeYParser.MetaIdContext ctx) {
        String id = visitSimple_ident(ctx.simple_ident());
        TermTransformer v = AbstractTermTransformer.name2metaop(id);
        if (v == null) {
            semanticError(ctx, "Unknown metaoperator: " + id);
        }
        return v;
    }

    @Override
    public JTerm visitMetaTerm(KeYParser.MetaTermContext ctx) {
        Operator metaId = accept(ctx.metaId());
        List<JTerm> t = mapOf(ctx.term());
        return capsulateTf(ctx, () -> getTermFactory().createTerm(metaId, t));
    }

    public JTerm createAttributeTerm(JTerm prefix, Operator attribute, ParserRuleContext ctx) {
        JTerm result = prefix;

        if (attribute instanceof JOperatorSV sv) {
            /*
             * if (!inSchemaMode()) { semanticError(null,
             * "Schemavariables may only occur inside taclets."); }
             */
            if (sv.sort() instanceof ProgramSVSort
                    || sv.sort() == AbstractTermTransformer.METASORT) {
                semanticError(null, "Cannot use schema variable " + sv + " as an attribute");
            }
            result = getServices().getTermBuilder().select(sv.sort(),
                getServices().getTermBuilder().getBaseHeap(), prefix,
                capsulateTf(ctx, () -> getTermFactory().createTerm(attribute)));
        } else {
            if (attribute instanceof LogicVariable) {
                JTerm attrTerm = capsulateTf(ctx, () -> getTermFactory().createTerm(attribute));
                result = getServices().getTermBuilder().dot(JavaDLTheory.ANY, result, attrTerm);
            } else if (attribute instanceof ProgramConstant) {
                result = capsulateTf(ctx, () -> getTermFactory().createTerm(attribute));
            } else if (attribute == getServices().getJavaInfo().getArrayLength()) {
                JTerm finalResult = result;
                result =
                    capsulateTf(ctx, () -> getServices().getTermBuilder().dotLength(finalResult));
            } else {
                ProgramVariable pv = (ProgramVariable) attribute;
                Function fieldSymbol = getServices().getTypeConverter().getHeapLDT()
                        .getFieldSymbolForPV((LocationVariable) pv, getServices());
                if (pv.isFinal() && FinalHeapResolution
                        .isFinalEnabled(getServices().getProof().getSettings())) {
                    if (pv.isStatic()) {
                        result =
                            getServices().getTermBuilder().staticFinalDot(pv.sort(), fieldSymbol);
                    } else {
                        result =
                            getServices().getTermBuilder().finalDot(pv.sort(), result, fieldSymbol);
                    }
                } else if (pv.isStatic()) {
                    result = getServices().getTermBuilder().staticDot(pv.sort(), fieldSymbol);
                }

                else {
                    result = getServices().getTermBuilder().dot(pv.sort(), result, fieldSymbol);
                }
            }
        }
        return result;
    }

    private Operator getAttributeInPrefixSort(Sort prefixSort, String attributeName) {
        final JavaInfo javaInfo = getJavaInfo();

        Operator result = (JOperatorSV) schemaVariables().lookup(new Name(attributeName));
        // if (result == null) {

        final boolean unambigousAttributeName = attributeName.indexOf(':') != -1;

        if (unambigousAttributeName) {
            result = javaInfo.getAttribute(attributeName);
        } else if (attributeName.equals("length")) {
            try {
                result = javaInfo.getArrayLength();
            } catch (Exception ex) {
                throw new BuildingException(ex);
            }
        } else if (attributeName.equals("<inv>")) {
            // The invariant observer "<inv>" is implicit and not part of the class declaration
            // A special case is needed, hence.
            result = javaInfo.getInvProgramVar();
        } else if (attributeName.equals("<inv_free>")) {
            result = javaInfo.getFreeInvProgramVar();
        } else {
            final KeYJavaType prefixKJT = javaInfo.getKeYJavaType(prefixSort);
            if (prefixKJT == null) {
                semanticError(null,
                    "Could not find type '" + prefixSort + "'. Maybe mispelled or "
                        + "you use an array or object type in a .key-file with missing "
                        + "\\javaSource section.");
            }

            ProgramVariable var =
                javaInfo.getCanonicalFieldProgramVariable(attributeName, prefixKJT);
            if (var == null) {
                LogicVariable logicalvar =
                    (LogicVariable) namespaces().variables().lookup(attributeName);
                if (logicalvar == null) {
                    semanticError(null, "There is no attribute '%s' declared in type '%s' and no "
                        + "logical variable of that name.", attributeName, prefixSort);
                } else {
                    result = logicalvar;
                }
            } else {
                result = var;
            }
        }
        // }

        if (result == null && !("length".equals(attributeName))) {
            throwEx(new NotDeclException("Attribute ", attributeName));
        }
        return result;
    }

    /*
     * @Override public String visitAttrid(KeYParser.AttridContext ctx) { return ctx.getText(); }
     */

    private String unescapeString(String string) {
        char[] chars = string.toCharArray();
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < chars.length; i++) {
            if (chars[i] == '\\' && i < chars.length - 1) {
                switch (chars[++i]) {
                    case 'n' -> sb.append("\n");
                    case 'f' -> sb.append("\f");
                    case 'r' -> sb.append("\r");
                    case 't' -> sb.append("\t");
                    case 'b' -> sb.append("\b");
                    case ':' -> sb.append("\\:");
                    // this is so in KeY ...
                    default -> sb.append(chars[i]);
                    // this more relaxed than before, \a becomes a ...
                }
            } else {
                sb.append(chars[i]);
            }
        }
        return sb.toString();
    }

    @Override
    public JTerm visitString_literal(KeYParser.String_literalContext ctx) {
        String s = unescapeString(ctx.id.getText());
        return getServices().getTypeConverter().convertToLogicElement(new StringLiteral(s));
    }

    @Override
    public Object visitCast_term(KeYParser.Cast_termContext ctx) {
        JTerm result = accept(ctx.sub);
        if (ctx.sortId() == null) {
            return result;
        }

        Sort s = accept(ctx.sortId());
        Sort objectSort = getServices().getJavaInfo().objectSort();
        if (s == null) {
            semanticError(ctx, "Tried to cast to unknown type.");
        } else if (objectSort != null && !s.extendsTrans(objectSort)
                && result.sort().extendsTrans(objectSort)) {
            semanticError(ctx, "Illegal cast from " + result.sort() + " to sort " + s
                + ". Casts between primitive and reference types are not allowed. ");
        }
        assert s != null;
        SortDependingFunction castSymbol =
            getServices().getJavaDLTheory().getCastSymbol(s, services);
        return getTermFactory().createTerm(castSymbol, result);
    }

    private void markHeapAsExplicit(JTerm a) {
        explicitHeap.add(a);
        a.subs().forEach(this::markHeapAsExplicit);
    }

    /*
     * private Term createStaticAttributeOrMethod(JavaQuery jq, KeYParser.AccesstermContext ctx) {
     * final var kjt = jq.kjt; String mn = jq.attributeNames; if (jq.maybeAttr != null) {
     * ProgramVariable maybeAttr = getJavaInfo().getAttribute(mn, kjt); if (maybeAttr != null) { var
     * op = getAttributeInPrefixSort(kjt.getSort(), mn); return createAttributeTerm(null, op, ctx);
     * } } else { var suffix = ctx.atom_suffix(ctx.atom_suffix().size() - 1); for (IProgramMethod pm
     * : getJavaInfo().getAllProgramMethods(kjt)) { if (pm != null && pm.isStatic() &&
     * pm.name().toString().equals(kjt.getFullName() + "::" + mn)) { List<Term> arguments =
     * mapOf(suffix.attribute_or_query_suffix().result.args.argument()); Term[] args =
     * arguments.toArray(new Term[0]); return getJavaInfo().getStaticProgramMethodTerm(mn, args,
     * kjt.getFullName()); } } } assert false; return null; }
     */

    @Override
    public Object visitBracket_access_heap_update(KeYParser.Bracket_access_heap_updateContext ctx) {
        JTerm heap = pop();
        JTerm target = accept(ctx.target);
        JTerm val = accept(ctx.val);
        JTerm objectTerm = target.sub(1);
        JTerm fieldTerm = target.sub(2);
        return getServices().getTermBuilder().store(heap, objectTerm, fieldTerm, val);
    }


    @Override
    public Object visitBracket_access_heap_term(KeYParser.Bracket_access_heap_termContext ctx) {
        JTerm heap = pop();

        String id = accept(ctx.simple_ident());
        List<JTerm> args = accept(ctx.args);
        Function f = functions().lookup(new Name(id));
        if (f == null) {
            semanticError(ctx, "Unknown heap constructor " + id);
        }
        JTerm[] arguments = args.toArray(new JTerm[0]);
        JTerm[] augmentedArgs = new JTerm[args.size() + 1];
        System.arraycopy(arguments, 0, augmentedArgs, 1, arguments.length);
        augmentedArgs[0] = heap;
        JTerm result = capsulateTf(ctx, () -> getTermFactory().createTerm(f, augmentedArgs));
        if (!result.sort().name().toString().equals("Heap")) {
            semanticError(ctx, id + " is not a heap constructor ");
        }
        return result;
    }

    @Override
    public Object visitBracket_access_star(KeYParser.Bracket_access_starContext ctx) {
        JTerm reference = pop();
        JTerm rangeFrom = toZNotation("0", functions());
        JTerm lt = getServices().getTermBuilder().dotLength(reference);
        JTerm one = toZNotation("1", functions());
        JTerm rangeTo =
            getTermFactory().createTerm(functions().lookup(new Name("sub")), lt, one);
        // TODO construct
        return null;
    }

    @Override
    public Object visitBracket_access_indexrange(KeYParser.Bracket_access_indexrangeContext ctx) {
        // | term LBRACKET indexTerm=term (DOTRANGE rangeTo=term)? RBRACKET
        // #bracket_access_indexrange
        JTerm term = pop();
        boolean sequenceAccess = term.sort().name().toString().equalsIgnoreCase("seq");
        // boolean heapUpdate = reference.sort().name().toString().equalsIgnoreCase("Heap");

        if (sequenceAccess) {
            if (ctx.rangeTo != null) {
                semanticError(ctx, "Range access for sequence terms not allowed");
            }
            JTerm indexTerm = accept(ctx.indexTerm);
            assert indexTerm != null;
            if (!isIntTerm(indexTerm)) {
                semanticError(ctx,
                    "Expecting term of sort %s as index of sequence %s, but found: %s",
                    IntegerLDT.NAME, term, indexTerm);
            }
            return getServices().getTermBuilder().seqGet(JavaDLTheory.ANY, term, indexTerm);
        }

        if (ctx.rangeTo != null) {
            JTerm rangeFrom = accept(ctx.indexTerm);
            JTerm rangeTo = accept(ctx.rangeTo);
            if (rangeTo != null) {
                if (quantifiedArrayGuard == null) {
                    semanticError(ctx,
                        "Quantified array expressions are only allowed in locations.");
                }
                LogicVariable indexVar =
                    new LogicVariable(new Name("i"), sorts().lookup(new Name("int")));
                JTerm indexTerm = capsulateTf(ctx, () -> getTermFactory().createTerm(indexVar));

                Function leq = functions().lookup(new Name("leq"));
                JTerm fromTerm =
                    capsulateTf(ctx, () -> getTermFactory().createTerm(leq, rangeFrom, indexTerm));
                JTerm toTerm =
                    capsulateTf(ctx, () -> getTermFactory().createTerm(leq, indexTerm, rangeTo));
                JTerm guardTerm = capsulateTf(ctx,
                    () -> getTermFactory().createTerm(Junctor.AND, fromTerm, toTerm));
                quantifiedArrayGuard = capsulateTf(ctx, () -> getTermFactory()
                        .createTerm(Junctor.AND, quantifiedArrayGuard, guardTerm));
                // TODO check quantifiedArrayGuard!
            }
        }
        JTerm indexTerm = accept(ctx.indexTerm);
        return capsulateTf(ctx, () -> getServices().getTermBuilder().dotArr(term, indexTerm));
    }

    @Override
    public Object visitBoolean_literal(KeYParser.Boolean_literalContext ctx) {
        if (ctx.TRUE() != null) {
            return capsulateTf(ctx, () -> getTermFactory().createTerm(Junctor.TRUE));
        } else {
            return capsulateTf(ctx, () -> getTermFactory().createTerm(Junctor.FALSE));
        }
    }

    @Override
    public Object visitPrimitive_labeled_term(KeYParser.Primitive_labeled_termContext ctx) {
        JTerm t = accept(ctx.primitive_term());
        if (ctx.LGUILLEMETS() != null) {
            ImmutableArray<TermLabel> labels = accept(ctx.label());
            if (!labels.isEmpty()) {
                t = getServices().getTermBuilder().addLabel(t, labels);
            }
        }
        return updateOrigin(t, ctx, services);
    }

    @Override
    public ImmutableArray<TermLabel> visitLabel(KeYParser.LabelContext ctx) {
        List<TermLabel> labels = mapOf(ctx.single_label());
        return new ImmutableArray<>(labels);
    }

    @Override
    public TermLabel visitSingle_label(KeYParser.Single_labelContext ctx) {
        String labelName = "";
        TermLabel left = null;
        TermLabel right = null;

        if (ctx.IDENT() != null) {
            labelName = ctx.IDENT().getText();
        }
        if (ctx.STAR() != null) {
            labelName = ctx.STAR().getText();
        }

        TermLabel label = null;
        List<String> parameters = mapOf(ctx.string_value());
        try {
            SchemaVariable var = schemaVariables().lookup(new Name(labelName));
            if (var instanceof TermLabel) {
                label = (TermLabel) var;
            }
            if (label == null) {
                label = getServices().getProfile().getTermLabelManager().parseLabel(labelName,
                    parameters, getServices());
            }
        } catch (Exception ex) {
            throw new BuildingException(ctx, ex);
        }
        return label;
    }

    @Override
    public Object visitAbbreviation(KeYParser.AbbreviationContext ctx) {
        String sc = accept(ctx.name);
        JTerm a = abbrevMap.getTerm(sc);
        if (a == null) {
            throwEx(new NotDeclException("abbreviation", sc));
        }
        return a;
    }

    @Override
    public JTerm visitIfThenElseTerm(KeYParser.IfThenElseTermContext ctx) {
        JTerm condF = (JTerm) ctx.condF.accept(this);
        if (condF.sort() != JavaDLTheory.FORMULA) {
            semanticError(ctx, "Condition of an \\if-then-else term has to be a formula.");
        }
        JTerm thenT = (JTerm) ctx.thenT.accept(this);
        JTerm elseT = (JTerm) ctx.elseT.accept(this);
        return capsulateTf(ctx,
            () -> getTermFactory().createTerm(IfThenElse.IF_THEN_ELSE, condF, thenT, elseT));
    }


    @Override
    public Object visitIfExThenElseTerm(KeYParser.IfExThenElseTermContext ctx) {
        Namespace<QuantifiableVariable> orig = variables();
        List<QuantifiableVariable> exVars = accept(ctx.bound_variables());
        JTerm condF = accept(ctx.condF);
        if (condF.sort() != JavaDLTheory.FORMULA) {
            semanticError(ctx, "Condition of an \\ifEx-then-else term has to be a formula.");
        }

        JTerm thenT = accept(ctx.thenT);
        JTerm elseT = accept(ctx.elseT);
        ImmutableArray<QuantifiableVariable> exVarsArray = new ImmutableArray<>(exVars);
        JTerm result = getTermFactory().createTerm(IfExThenElse.IF_EX_THEN_ELSE,
            new JTerm[] { condF, thenT, elseT }, exVarsArray, null);
        unbindVars(orig);
        return result;
    }

    @Override
    public JTerm visitQuantifierterm(KeYParser.QuantifiertermContext ctx) {
        Operator op = null;
        Namespace<QuantifiableVariable> orig = variables();
        if (ctx.FORALL() != null) {
            op = Quantifier.ALL;
        }
        if (ctx.EXISTS() != null) {
            op = Quantifier.EX;
        }
        List<QuantifiableVariable> vs = accept(ctx.bound_variables());
        JTerm a1 = accept(ctx.sub);
        JTerm a = getTermFactory().createTerm(op, new ImmutableArray<>(a1),
            new ImmutableArray<>(vs.toArray(new QuantifiableVariable[0])), null);
        unbindVars(orig);
        return a;
    }

    @Override
    public JTerm visitLocset_term(KeYParser.Locset_termContext ctx) {
        List<JTerm> terms = mapOf(ctx.location_term());
        return getServices().getTermBuilder().union(terms);
    }

    @Override
    public Object visitLocation_term(KeYParser.Location_termContext ctx) {
        JTerm obj = accept(ctx.obj);
        JTerm field = accept(ctx.field);
        return getServices().getTermBuilder().singleton(obj, field);
    }

    @Override
    public Object visitSubstitution_term(KeYParser.Substitution_termContext ctx) {
        SubstOp op = WarySubstOp.SUBST;
        Namespace<QuantifiableVariable> orig = variables();
        JAbstractSortedOperator v = accept(ctx.bv);
        unbindVars(orig);
        if (v instanceof LogicVariable) {
            bindVar((LogicVariable) v);
        } else {
            bindVar();
        }

        JTerm a1 = accept(ctx.replacement);
        JTerm a2 = oneOf(ctx.atom_prefix(), ctx.unary_formula());
        try {
            JTerm result =
                getServices().getTermBuilder().subst(op, (QuantifiableVariable) v, a1, a2);
            return result;
        } catch (Exception e) {
            throw new BuildingException(ctx, e);
        } finally {
            unbindVars(orig);
        }
    }

    @Override
    public Object visitUpdate_term(KeYParser.Update_termContext ctx) {
        JTerm t = oneOf(ctx.atom_prefix(), ctx.unary_formula());
        if (ctx.u.isEmpty()) {
            return t;
        }
        JTerm u = accept(ctx.u);
        return getTermFactory().createTerm(UpdateApplication.UPDATE_APPLICATION, u, t);
    }

    public List<QuantifiableVariable> visitBound_variables(KeYParser.Bound_variablesContext ctx) {
        return mapOf(ctx.one_bound_variable());
    }

    @Override
    public QuantifiableVariable visitOne_bound_variable(KeYParser.One_bound_variableContext ctx) {
        String id = accept(ctx.simple_ident());
        Sort sort = accept(ctx.sortId());

        SchemaVariable ts = schemaVariables().lookup(new Name(id));
        if (ts != null) {
            if (!(ts instanceof VariableSV)) {
                semanticError(ctx,
                    ts + " is not allowed in a quantifier. Note, that you can't "
                        + "use the normal syntax for quantifiers of the form \"\\exists int i;\""
                        + " in taclets. You have to define the variable as a schema variable"
                        + " and use the syntax \"\\exists i;\" instead.");
            }
            bindVar();
            return (QuantifiableVariable) ts;
        }

        if (sort != null && id != null) {
            return bindVar(id, sort);
        }

        QuantifiableVariable result =
            doLookup(new Name(ctx.id.getText()), variables());

        if (result == null) {
            semanticError(ctx, "There is no schema variable or variable named " + id);
        }

        return result;
    }


    @Override
    public Object visitModality_term(KeYParser.Modality_termContext ctx) {
        JTerm a1 = accept(ctx.sub);
        if (ctx.MODALITY() == null) {
            return a1;
        }

        PairOfStringAndJavaBlock sjb = getJavaBlock(ctx.MODALITY().getSymbol());
        Operator op;
        if (sjb.opName.charAt(0) == '#') {
            /*
             * if (!inSchemaMode()) { semanticError(ctx,
             * "No schema elements allowed outside taclet declarations (" + sjb.opName + ")"); }
             */
            JModality.JavaModalityKind kind =
                (JModality.JavaModalityKind) schemaVariables().lookup(new Name(sjb.opName));
            op = JModality.getModality(kind, sjb.javaBlock);
        } else {
            JModality.JavaModalityKind kind = JModality.JavaModalityKind.getKind(sjb.opName);
            op = JModality.getModality(kind, sjb.javaBlock);
        }
        if (op == null) {
            semanticError(ctx, "Unknown modal operator: " + sjb.opName);
        }

        return capsulateTf(ctx,
            () -> getTermFactory().createTerm(op, new JTerm[] { a1 }, null, null));
    }

    @Override
    public List<JTerm> visitArgument_list(KeYParser.Argument_listContext ctx) {
        return mapOf(ctx.term());
    }

    @Override
    public Object visitChar_literal(KeYParser.Char_literalContext ctx) {
        String s = ctx.CHAR_LITERAL().getText();
        int intVal = 0;
        if (s.length() == 3) {
            intVal = s.charAt(1);
        } else {
            try {
                intVal = Integer.parseInt(s.substring(3, s.length() - 1), 16);
            } catch (NumberFormatException ex) {
                semanticError(ctx, "'" + s + "' is not a valid character.");
            }
        }
        return getTermFactory().createTerm(functions().lookup(new Name("C")),
            toZNotation(String.valueOf(intVal), functions()).sub(0));
    }

    public boolean isClass(String p) {
        return getJavaInfo().getTypeByClassName(p) != null;
    }

    /**
     * Handles "[sort]::a.name.or.something.else"
     *
     * @param ctx
     * @return a Term or an operator, depending on the referenced object.
     */
    @Override
    public Object visitFuncpred_name(KeYParser.Funcpred_nameContext ctx) {
        Sort sortId = accept(ctx.sortId());
        List<String> parts = mapOf(ctx.name.simple_ident());
        String varfuncid = ctx.name.getText();

        if (ctx.INT_LITERAL() != null) {// number
            return toZNotation(ctx.INT_LITERAL().getText(), functions());
        }

        assert parts != null && varfuncid != null;

        boolean javaReference =
            parts.size() > 1 && (isPackage(parts.get(0)) || isClass(parts.get(0)));

        if (javaReference) {
            return splitJava(parts);
        }

        if ("skip".equals(varfuncid)) {
            return UpdateJunctor.SKIP;
        }

        Operator op;
        if (varfuncid.endsWith(LIMIT_SUFFIX)) {
            varfuncid = varfuncid.substring(0, varfuncid.length() - 5);
            op = lookupVarfuncId(ctx, varfuncid,
                ctx.sortId() != null ? ctx.sortId().getText() : null, sortId);
            if (ObserverFunction.class.isAssignableFrom(op.getClass())) {
                op = getServices().getSpecificationRepository()
                        .limitObs((ObserverFunction) op).first;
            } else {
                semanticError(ctx, "Cannot can be limited: " + op);
            }
        } else {
            String firstName =
                ctx.name == null ? ctx.INT_LITERAL().getText()
                        : ctx.name.simple_ident(0).getText();
            op = lookupVarfuncId(ctx, firstName,
                ctx.sortId() != null ? ctx.sortId().getText() : null, sortId);
            if (op instanceof ProgramVariable v && ctx.name.simple_ident().size() > 1) {
                List<KeYParser.Simple_identContext> otherParts =
                    ctx.name.simple_ident().subList(1, ctx.name.simple_ident().size());
                JTerm tv = getServices().getTermFactory().createTerm(v);
                String memberName = otherParts.get(0).getText();
                if (v.sort() == getServices().getTypeConverter().getSeqLDT().targetSort()) {
                    if ("length".equals(memberName)) {
                        return getServices().getTermBuilder().seqLen(tv);
                    } else {
                        semanticError(ctx, "There is no attribute '%s'for sequences (Seq), only "
                            + "'length' is supported.", memberName);
                    }
                }
                memberName = StringUtil.trim(memberName, "()");
                Operator attr = getAttributeInPrefixSort(v.sort(), memberName);
                return createAttributeTerm(tv, attr, ctx);
            }
        }
        return op;
    }

    private JTerm visitAccesstermAsJava(KeYParser.AccesstermContext ctx) {
        String firstName = accept(ctx.firstName);
        if (isPackage(firstName) || isClass(firstName)) {
            // consume suffix as long as it is part of a java class or package
            String javaPackage = isPackage(firstName) ? firstName : "";
            boolean startWithPackage = isPackage(firstName);
            String javaClass = isClass(firstName) ? firstName : "";

            int currentSuffix = 0;

            // region split up package and class name
            while (startWithPackage
                    && ctx.attribute(
                        currentSuffix) instanceof KeYParser.Attribute_simpleContext a) {
                if (a.heap != null) {
                    break; // No heap on java package allowed
                }
                @Nullable
                Object cur = accept(a.id);
                if (isPackage(javaPackage + "." + cur)) {
                    javaPackage += "." + cur;
                    currentSuffix++;
                } else {
                    break;
                }
            }

            while (ctx.attribute(currentSuffix) instanceof KeYParser.Attribute_simpleContext a) {
                if (a.heap != null) {
                    break; // No heap on java Class name allowed
                }
                String cur = accept(a.id);
                String candidate = javaClass.isEmpty() ? cur : (javaClass + "." + cur);
                if (isClass(javaPackage + (javaPackage.isEmpty() ? "" : ".") + candidate)) {
                    javaClass = candidate;
                    currentSuffix++;
                } else {
                    break;
                }
            }
            // endregion

            KeYJavaType kjt =
                getTypeByClassName(javaPackage + (javaPackage.isEmpty() ? "" : ".") + javaClass);

            if (ctx.call() != null) {
                addWarning("Call of package or class");
            }

            JTerm current = null;
            for (int i = currentSuffix; i < ctx.attribute().size(); i++) {
                KeYParser.AttributeContext attrib = ctx.attribute(i);
                boolean isLast = i == ctx.attribute().size() - 1;

                if (attrib instanceof KeYParser.Attribute_simpleContext simpleContext) {
                    boolean isCall = simpleContext.call() != null;
                    ParserRuleContext heap = simpleContext.heap; // TODO?
                    String attributeName = accept(simpleContext.id);
                    ProgramVariable maybeAttr = getJavaInfo().getAttribute(attributeName, kjt);
                    if (maybeAttr != null) {
                        Operator op = getAttributeInPrefixSort(kjt.getSort(), attributeName);
                        current = createAttributeTerm(current, op, ctx);
                    } else {
                        IProgramMethod pm = getStaticQuery(kjt, attributeName);
                        if (pm != null) {
                            JTerm[] args = visitArguments(simpleContext.call().argument_list());
                            current = getJavaInfo().getStaticProgramMethodTerm(attributeName, args,
                                kjt.getFullName());
                        } else {
                            semanticError(ctx, "Unknown java attribute: %s", attributeName);
                        }
                        // TODO If not last attribute:
                        addWarning("");
                        return current;
                    }
                } else if (attrib instanceof KeYParser.Attribute_complexContext attrid) {
                    String className = attrid.sort.getText();
                    String attributeName = attrid.id.getText();
                    JTerm[] args = visitArguments(attrid.call().argument_list());
                    current = getServices().getJavaInfo().getStaticProgramMethodTerm(attributeName,
                        args, className);
                    if (current == null) {
                        final Sort sort = lookupSort(className);
                        if (sort == null) {
                            semanticError(ctx, "Could not find matching sort for " + className);
                        }
                        kjt = getServices().getJavaInfo().getKeYJavaType(sort);
                        if (kjt == null) {
                            semanticError(ctx, "Found logic sort for " + className
                                + " but no corresponding java type!");
                        }
                    }
                    return current;
                } else if (attrib instanceof KeYParser.Attribute_starContext) {
                    // TODO
                }
            }
            return current;
        }
        return null;
    }

    @Override
    public Object visitTermParen(KeYParser.TermParenContext ctx) {
        JTerm base = accept(ctx.term());
        if (ctx.attribute().isEmpty()) {
            return base;
        }
        return handleAttributes(base, ctx.attribute());
    }

    private JTerm handleAttributes(JTerm current, List<KeYParser.AttributeContext> attribute) {
        for (int i = 0; i < attribute.size(); i++) {
            KeYParser.AttributeContext ctxSuffix = attribute.get(i);
            boolean isLast = i == attribute.size() - 1;

            if (ctxSuffix instanceof KeYParser.Attribute_starContext) {
                current = services.getTermBuilder().allFields(current);
                if (!isLast) {
                    addWarning("");
                }
                return current;
            } else if (ctxSuffix instanceof KeYParser.Attribute_simpleContext attrid) {
                String memberName = attrid.id.getText();
                Sort seqSort = lookupSort("Seq");
                if (current.sort() == seqSort) {
                    if ("length".equals(memberName)) {
                        return getServices().getTermBuilder().seqLen(current);
                    } else {
                        semanticError(ctxSuffix, "There is no attribute '%s'for sequences (Seq), "
                            + "only 'length' is supported.", memberName);
                    }
                } else {
                    boolean isCall = attrid.call() != null;
                    JTerm[] sfxargs = isCall ? visitArguments(attrid.call().argument_list()) : null;
                    JTerm heap = accept(attrid.heap);
                    if (isCall) {
                        String classRef = current.sort().name().toString();
                        KeYJavaType kjt = getTypeByClassName(classRef); // Why not direct use of
                        // Sort?
                        if (kjt == null) {
                            semanticError(ctxSuffix, "Could not find sort for %s", classRef);
                        }
                        assert kjt != null;
                        classRef = kjt.getFullName();
                        current = getServices().getJavaInfo().getProgramMethodTerm(current,
                            memberName, sfxargs, classRef, true);
                    } else {
                        Operator attr = getAttributeInPrefixSort(current.sort(), memberName);
                        current = createAttributeTerm(current, attr, ctxSuffix);
                    }

                    if (heap != null) {
                        current = replaceHeap(current, heap, ctxSuffix);
                    }
                }
            } else if (ctxSuffix instanceof KeYParser.Attribute_complexContext attrid) {
                JTerm heap = accept(attrid.heap);
                String classRef = attrid.sort.getText();
                String memberName = attrid.id.getText();
                boolean isCall = attrid.call() != null;
                JTerm[] sfxargs = isCall ? visitArguments(attrid.call().argument_list()) : null;
                if (isCall) {
                    KeYJavaType kjt = getTypeByClassName(classRef); // Why not direct use of Sort?
                    if (kjt == null) {
                        semanticError(ctxSuffix, "Could not find sort for %s", classRef);
                    }
                    assert kjt != null;
                    classRef = kjt.getFullName();
                    current = getServices().getJavaInfo().getProgramMethodTerm(current, memberName,
                        sfxargs, classRef, false);
                } else {
                    Operator op = getAttributeInPrefixSort(getTypeByClassName(classRef).getSort(),
                        classRef + "::" + memberName);
                    current = createAttributeTerm(current, op, ctxSuffix);
                }

                if (current == null) {
                    final Sort sort = lookupSort(classRef);
                    if (sort == null) {
                        semanticError(ctxSuffix, "Could not find matching sort for %s", classRef);
                    }
                    KeYJavaType kjt = getServices().getJavaInfo().getKeYJavaType(sort);
                    if (kjt == null) {
                        semanticError(ctxSuffix,
                            "Found logic sort for %s but no corresponding java type!", classRef);
                    }
                }
                if (heap != null) {
                    current = replaceHeap(current, heap, ctxSuffix);
                }
            }
        }
        return current;
    }

    public <T> T defaultOnException(T defaultValue, Supplier<T> supplier) {
        try {
            return supplier.get();
        } catch (Exception e) {
            return defaultValue;
        }
    }

    @Override
    public JTerm visitAccessterm(KeYParser.AccesstermContext ctx) {
        JTerm t = visitAccesstermAsJava(ctx);
        if (t != null) {
            return t;
        }

        // weigl: I am unsure if this is wise.
        Sort sortId = defaultOnException(null, () -> accept(ctx.sortId()));
        String firstName = accept(ctx.simple_ident());

        ImmutableArray<QuantifiableVariable> boundVars = null;
        Namespace<QuantifiableVariable> orig = null;
        JTerm[] args = null;
        if (ctx.call() != null) {
            orig = variables();
            List<QuantifiableVariable> bv = accept(ctx.call().boundVars);
            boundVars =
                bv != null ? new ImmutableArray<>(bv.toArray(new QuantifiableVariable[0])) : null;
            args = visitArguments(ctx.call().argument_list());
            if (boundVars != null) {
                unbindVars(orig);
            }
        }

        assert firstName != null;
        Operator op;

        if ("skip".equals(firstName)) {
            op = UpdateJunctor.SKIP;
        } else if (firstName.endsWith(LIMIT_SUFFIX)) {
            firstName = firstName.substring(0, firstName.length() - 5);
            op = lookupVarfuncId(ctx, firstName,
                ctx.sortId() != null ? ctx.sortId().getText() : null, sortId);
            if (ObserverFunction.class.isAssignableFrom(op.getClass())) {
                op = getServices().getSpecificationRepository()
                        .limitObs((ObserverFunction) op).first;
            } else {
                semanticError(ctx, "Cannot can be limited: " + op);
            }
        } else {
            op = lookupVarfuncId(ctx, firstName,
                ctx.sortId() != null ? ctx.sortId().getText() : null, sortId);
        }

        JTerm current;
        Operator finalOp = op;
        if (op instanceof ParsableVariable) {
            if (args != null) {
                semanticError(ctx, "You used the variable `%s` like a predicate or function.", op);
            }
            if (boundVars != null) {
                addWarning(ctx, "Bounded variable are ignored on a variable");
            }
            current = termForParsedVariable((ParsableVariable) op, ctx);
        } else {
            if (boundVars == null) {
                JTerm[] finalArgs = args;
                current = capsulateTf(ctx, () -> getTermFactory().createTerm(finalOp, finalArgs));
            } else {
                // sanity check
                assert op instanceof Function;
                for (int i = 0; i < args.length; i++) {
                    if (i < op.arity() && !op.bindVarsAt(i)) {
                        for (QuantifiableVariable qv : args[i].freeVars()) {
                            if (boundVars.contains(qv)) {
                                semanticError(ctx,
                                    "Building function term " + op
                                        + " with bound variables failed: " + "Variable " + qv
                                        + " must not occur free in subterm " + args[i]);
                            }
                        }
                    }
                }
                ImmutableArray<QuantifiableVariable> finalBoundVars = boundVars;
                // create term
                JTerm[] finalArgs1 = args;
                current = capsulateTf(ctx,
                    () -> getTermFactory().createTerm(finalOp, finalArgs1, finalBoundVars, null));
            }
        }
        current = handleAttributes(current, ctx.attribute());
        return current;
    }

    private @Nullable JTerm[] visitArguments(KeYParser.@Nullable Argument_listContext call) {
        List<JTerm> arguments = accept(call);
        return arguments == null ? null : arguments.toArray(new JTerm[0]);
    }

    @Override
    public Object visitFloatLiteral(FloatLiteralContext ctx) {
        String txt = ctx.getText(); // full text of node incl. unary minus.
        return toFPNotation(txt);
    }

    @Override
    public Object visitDoubleLiteral(DoubleLiteralContext ctx) {
        String txt = ctx.getText(); // full text of node incl. unary minus.
        return toDFPNotation(txt.substring(0, txt.length() - 1));
    }

    @Override
    public Object visitRealLiteral(RealLiteralContext ctx) {
        String txt = ctx.getText(); // full text of node incl. unary minus.
        char lastChar = txt.charAt(txt.length() - 1);
        if (lastChar == 'R' || lastChar == 'r') {
            semanticError(ctx,
                "The given float literal does not have a suffix. This is essential to determine its exact meaning. You probably want to add 'r' as a suffix.");
        }
        throw new Error("not yet implemented");
    }

    @Override
    public Object visitInteger(KeYParser.IntegerContext ctx) {
        return toZNotation(ctx.getText());
    }

    private JTerm toZNotation(String number) {
        return getTermFactory().createTerm(functions().lookup(new Name("Z")),
            toNum(number));
    }

    private JTerm toCNotation(String number) {
        return getTermFactory().createTerm(functions().lookup(new Name("C")),
            toNum(number));
    }

    private JTerm toFPNotation(String number) {
        String decBitString =
            Integer.toUnsignedString(Float.floatToIntBits(Float.parseFloat(number)));
        // toNum("0")); // soon to disappear
        return getTermFactory().createTerm(functions().lookup(new Name("FP")),
            toNum(decBitString));
    }

    private JTerm toDFPNotation(String number) {
        String decBitString =
            Long.toUnsignedString(Double.doubleToLongBits(Double.parseDouble(number)));
        return getTermFactory().createTerm(functions().lookup(new Name("DFP")),
            toNum(decBitString)); // toNum("0")); // soon to disappear
    }

    private JTerm toNum(String number) {
        String s = number;
        final boolean negative = (s.charAt(0) == '-');
        if (negative) {
            s = number.substring(1, s.length());
        }
        if (s.startsWith("0x")) {
            try {
                BigInteger bi = new BigInteger(s.substring(2), 16);
                s = bi.toString();
            } catch (NumberFormatException nfe) {
                Debug.fail("Not a hexadecimal constant (BTW, this should not have happened).");
            }
        }
        JTerm result = getTermFactory().createTerm(functions().lookup(new Name("#")));

        for (int i = 0; i < s.length(); i++) {
            result = getTermFactory()
                    .createTerm(functions().lookup(new Name(s.substring(i, i + 1))),
                        result);
        }

        if (negative) {
            result = getTermFactory().createTerm(functions().lookup(new Name("neglit")),
                result);
        }

        return result;
    }

    /*
     * private Term makeBinaryTerm(String opName, Term a, Term a1) { LDT ldt =
     * services.getTypeConverter().getLDTFor(a.sort()); if (ldt != null) { Function op =
     * ldt.getFunctionFor(opName, services); if (op == null) {
     * semanticError("Cannot resolve symbol '" + opName + "' for sort " + a.sort()); } else { a =
     * getTermFactory().createTerm(op, a, a1); return a; } } Function op = (Function)
     * functions().lookup(new Name(opName)); if(op == null) { semanticError("Function symbol '" +
     * opName + "' not found."); } a = getTermFactory().createTerm(op, a, a1); return a; }
     */


    private JTerm termForParsedVariable(ParsableVariable v, ParserRuleContext ctx) {
        if (v instanceof LogicVariable lv) {
            return capsulateTf(ctx, () -> getTermFactory().createTerm(lv));
        } else if (v instanceof LocationVariable lv) {
            return capsulateTf(ctx, () -> getTermFactory().createTerm(lv));
        } else {
            if (v instanceof JOperatorSV sv) {
                return capsulateTf(ctx, () -> getTermFactory().createTerm(sv));
            } else {
                String errorMessage = "";
                if (false) {
                    errorMessage += v + " is not a program, logic or schema variable";
                } else {
                    errorMessage += v + " is not a logic or program variable";
                }
                semanticError(null, errorMessage);
            }
        }
        return null;
    }

    public TermFactory getTermFactory() {
        return getServices().getTermFactory();
    }


    protected ImmutableSet<JModality.JavaModalityKind> opSVHelper(String opName,
            ImmutableSet<JModality.JavaModalityKind> modalityKinds) {
        if (opName.charAt(0) == '#') {
            return lookupOperatorSV(opName, modalityKinds);
        } else {
            JModality.JavaModalityKind m = JModality.JavaModalityKind.getKind(opName);
            if (m == null) {
                semanticError(null, "Unrecognised operator: " + opName);
            }
            modalityKinds = modalityKinds.add(m);
        }
        return modalityKinds;
    }


    private String getTypeList(ImmutableList<ProgramVariable> vars) {
        StringBuilder result = new StringBuilder();
        final Iterator<ProgramVariable> it = vars.iterator();
        while (it.hasNext()) {
            result.append(it.next().getContainerType().getFullName());
            if (it.hasNext()) {
                result.append(", ");
            }
        }
        return result.toString();
    }

    KeYJavaType getTypeByClassName(String s) {
        KeYJavaType kjt = null;
        try {
            kjt = getJavaInfo().getTypeByClassName(s, null);
        } catch (RuntimeException e) {
            return null;
        }

        return kjt;
    }

    private boolean isPackage(String name) {
        try {
            return getJavaInfo().isPackage(name);
        } catch (RuntimeException e) {
            // may be thrown in cases of invalid java identifiers
            return false;
        }
    }

    protected boolean isHeapTerm(JTerm term) {
        return term != null
                && term.sort() == getServices().getTypeConverter().getHeapLDT().targetSort();
    }

    private boolean isSequenceTerm(JTerm reference) {
        return reference != null && reference.sort().name().equals(SeqLDT.NAME);
    }

    private boolean isIntTerm(JTerm reference) {
        return reference.sort().name().equals(IntegerLDT.NAME);
    }

    private ImmutableSet<JModality.JavaModalityKind> lookupOperatorSV(String opName,
            ImmutableSet<JModality.JavaModalityKind> modalityKinds) {
        SchemaVariable sv = schemaVariables().lookup(new Name(opName));
        if (sv instanceof ModalOperatorSV osv) {
            modalityKinds = modalityKinds.union(osv.getModalities());
        } else {
            semanticError(null, "Schema variable " + opName + " not defined.");
        }
        return modalityKinds;
    }

    private boolean isImplicitHeap(JTerm t) {
        return getServices().getTermBuilder().getBaseHeap().equals(t);
    }

    /**
     * Guard for {@link #replaceHeap0(JTerm, JTerm, ParserRuleContext)} to protect the double
     * application of {@code @heap}.
     */
    private JTerm replaceHeap(JTerm term, JTerm heap, ParserRuleContext ctx) {
        if (explicitHeap.contains(term)) {
            return term;
        }
        JTerm t = replaceHeap0(term, heap, ctx);
        markHeapAsExplicit(t);
        return t;
    }

    private JTerm replaceHeap0(JTerm term, JTerm heap, ParserRuleContext ctx) {
        if (isSelectTerm(term)) {
            if (!isImplicitHeap(term.sub(0))) {
                // semanticError(null, "Expecting program variable heap as first argument of: %s",
                // term);
                return term;
            }
            JTerm[] params = { heap, replaceHeap(term.sub(1), heap, ctx), term.sub(2) };
            return capsulateTf(ctx,
                () -> getServices().getTermFactory().createTerm(term.op(), params));
        } else if (term.op() instanceof ObserverFunction) {
            if (!isImplicitHeap(term.sub(0))) {
                semanticError(null, "Expecting program variable heap as first argument of: %s",
                    term);
            }

            JTerm[] params = new JTerm[term.arity()];
            params[0] = heap;
            params[1] = replaceHeap(term.sub(1), heap, ctx);
            for (int i = 2; i < params.length; i++) {
                params[i] = term.sub(i);
            }

            return capsulateTf(ctx,
                () -> getServices().getTermFactory().createTerm(term.op(), params));

        }
        return term;
    }

    /**
     * Replace standard heap by another heap in an observer function.
     */
    protected JTerm heapSelectionSuffix(JTerm term, JTerm heap, ParserRuleContext ctx) {
        if (!isHeapTerm(heap)) {
            semanticError(null, "Expecting term of type Heap but sort is %s for term %s",
                heap.sort(), term);
        }
        JTerm result = replaceHeap(term, heap, ctx);
        return result;
    }

    private IProgramMethod getStaticQuery(String className, String methodName) {
        KeYJavaType kjt = getTypeByClassName(className);
        return getStaticQuery(kjt, methodName);
    }

    private IProgramMethod getStaticQuery(KeYJavaType kjt, String methodName) {
        if (kjt != null) {
            final JavaInfo javaInfo = getJavaInfo();
            final String name = kjt.getFullName() + "::" + methodName;
            for (IProgramMethod pm : javaInfo.getAllProgramMethods(kjt)) {
                if (pm != null && pm.isStatic() && pm.name().toString().equals(name)) {
                    return pm;
                }
            }
        }
        return null;
    }

    private JavaQuery splitJava(List<String> parts) {
        String packageName = null;
        String className = null;
        List<String> attributeName = null;
        int i = 0;
        for (; i < parts.size(); i++) {
            String test = parts.stream().limit(i).collect(Collectors.joining("."));
            if (isPackage(test)) {
                packageName = test;
            } else if (packageName != null) {
                break;
            }
        }

        KeYJavaType kjt = null;
        final long packageEnd = i - 1;
        for (i = 0; i < parts.size(); i++) {
            String test = parts.stream()
                    // .skip(packageEnd)
                    .limit(i + packageEnd).collect(Collectors.joining("."));
            kjt = getTypeByClassName(test);
            if (kjt != null) {
                className = test;
            } else if (className != null) {
                kjt = getTypeByClassName(className);
                break;
            }
        }
        int classEnd = i - 1;
        attributeName = parts.stream().skip(classEnd).collect(Collectors.toList());
        return (new JavaQuery(packageName, className, attributeName, kjt));
    }

    @Override
    public Object visitProofScript(KeYParser.ProofScriptContext ctx) {
        return null;// Do not traverse into proof scripts.
    }

    public void setAbbrevMap(AbbrevMap abbrevMap) {
        this.abbrevMap = abbrevMap;
    }

    public AbbrevMap getAbbrevMap() {
        return abbrevMap;
    }

    private static class PairOfStringAndJavaBlock {
        String opName;
        JavaBlock javaBlock;
    }

    /*
     * private boolean isStaticAttribute(String dotName) { final JavaInfo javaInfo = getJavaInfo();
     * String[] javaParts = splitJava(dotName); KeYJavaType kjt = getTypeByClassName(javaParts[1]);
     * if (kjt != null) { ProgramVariable maybeAttr = javaInfo.getAttribute(javaParts[2], kjt); if
     * (maybeAttr != null) { return true; } } return false; }
     */
}


record JavaQuery(String packageName, String className, List<String> attributeNames,
        KeYJavaType kjt) {
}
