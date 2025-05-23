/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.builder;

import java.util.*;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.varexp.ArgumentType;
import de.uka.ilkd.key.nparser.varexp.TacletBuilderCommand;
import de.uka.ilkd.key.nparser.varexp.TacletBuilderManipulators;
import de.uka.ilkd.key.parser.SchemaVariableModifierSet;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.conditions.TypeResolver;
import de.uka.ilkd.key.rule.tacletbuilder.*;
import de.uka.ilkd.key.util.parsing.BuildingException;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.*;

import antlr.RecognitionException;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.RuleContext;
import org.antlr.v4.runtime.Token;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static java.text.MessageFormat.format;

public class TacletPBuilder extends ExpressionBuilder {

    private static final Logger LOGGER = LoggerFactory.getLogger(TacletPBuilder.class);

    private final Deque<TacletBuilder<?>> currentTBuilder = new ArrayDeque<>(8);

    private Map<Taclet, TacletBuilder<? extends Taclet>> taclet2Builder = new HashMap<>();

    private boolean axiomMode;

    private final List<Taclet> topLevelTaclets = new ArrayList<>(2048);

    /**
     * Current required choices for taclets
     */
    private ChoiceExpr requiredChoices = ChoiceExpr.TRUE;

    /**
     * Required choices for taclet goals.
     */
    private ChoiceExpr goalChoice = ChoiceExpr.TRUE;

    public TacletPBuilder(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    public TacletPBuilder(Services services, NamespaceSet namespaces,
            Map<Taclet, TacletBuilder<? extends Taclet>> taclet2Builder) {
        this(services, namespaces);
        this.taclet2Builder = taclet2Builder;
    }

    @Override
    public Object visitDecls(KeYParser.DeclsContext ctx) {
        mapOf(ctx.schema_var_decls());
        mapOf(ctx.rulesOrAxioms());
        mapOf(ctx.datatype_decls());
        return null;
    }

    @Override
    public Object visitRulesOrAxioms(KeYParser.RulesOrAxiomsContext ctx) {
        enableJavaSchemaMode();
        if (ctx.RULES() != null) {
            axiomMode = false;
        }
        if (ctx.AXIOMS() != null) {
            axiomMode = true;
        }
        ChoiceExpr choices = accept(ctx.choices);
        this.requiredChoices = Objects.requireNonNullElse(choices, ChoiceExpr.TRUE);
        List<Taclet> seq = mapOf(ctx.taclet());
        topLevelTaclets.addAll(seq);
        disableJavaSchemaMode();
        return null;
    }

    @Override
    public Object visitOne_schema_modal_op_decl(KeYParser.One_schema_modal_op_declContext ctx) {
        ImmutableSet<Modality.JavaModalityKind> modalities = DefaultImmutableSet.nil();
        Sort sort = accept(ctx.sort);
        if (sort != null && sort != JavaDLTheory.FORMULA) {
            semanticError(ctx, "Modal operator SV must be a FORMULA, not " + sort);
        }
        List<String> ids = accept(ctx.simple_ident_comma_list());
        String id = accept(ctx.simple_ident());

        for (String s : Objects.requireNonNull(ids)) {
            modalities = opSVHelper(s, modalities);
        }
        SchemaVariable osv =
            SchemaVariableFactory.createModalOperatorSV(new Name(id), sort, modalities);
        schemaVariables().add(osv);
        return osv;
    }

    @Override
    public TacletBuilder<?> visitTriggers(KeYParser.TriggersContext ctx) {
        String id = (String) ctx.id.accept(this);
        OperatorSV triggerVar = (OperatorSV) schemaVariables().lookup(new Name(id));
        if (triggerVar == null) {
            semanticError(ctx, "Undeclared schemavariable: " + id);
        }
        TacletBuilder<?> b = peekTBuilder();
        Term t = accept(ctx.t);
        List<Term> avoidConditions = mapOf(ctx.avoidCond);
        b.setTrigger(new Trigger(triggerVar, t, ImmutableList.fromList(avoidConditions)));
        return null;
    }

    @Override
    public Taclet visitTaclet(KeYParser.TacletContext ctx) {
        Sequent ifSeq = Sequent.EMPTY_SEQUENT;
        ImmutableSet<TacletAnnotation> tacletAnnotations = DefaultImmutableSet.nil();
        if (ctx.LEMMA() != null) {
            tacletAnnotations = tacletAnnotations.add(de.uka.ilkd.key.rule.TacletAnnotation.LEMMA);
        }
        String name = ctx.name.getText();
        ChoiceExpr ch = accept(ctx.option_list());
        var choices = requiredChoices;
        if (ch != null) {
            choices = ChoiceExpr.and(ch, choices);
        }

        Term form = accept(ctx.form);
        if (form != null) {
            if (!axiomMode) {
                semanticError(ctx, "formula rules are only permitted for \\axioms");
            }
            TacletBuilder<?> b = createTacletBuilderFor(null, RewriteTaclet.NONE, ctx);
            currentTBuilder.push(b);
            SequentFormula sform = new SequentFormula(form);
            Semisequent semi = new Semisequent(sform);
            Sequent addSeq = Sequent.createAnteSequent(semi);
            ImmutableList<Taclet> noTaclets = ImmutableSLList.nil();
            DefaultImmutableSet<SchemaVariable> noSV = DefaultImmutableSet.nil();
            addGoalTemplate(null, null, addSeq, noTaclets, noSV, null, ctx);
            b.setName(new Name(name));
            b.setChoices(choices);
            b.setAnnotations(tacletAnnotations);
            b.setOrigin(BuilderHelpers.getPosition(ctx));
            Taclet r = b.getTaclet();
            registerTaclet(ctx, r);
            currentTBuilder.pop();
            return r;
        }

        // schema var decls
        setSchemaVariables(new Namespace<>(schemaVariables()));
        mapOf(ctx.one_schema_var_decl());

        if (ctx.ifSeq != null) {
            ifSeq = accept(ctx.ifSeq);
        }

        int applicationRestriction = RewriteTaclet.NONE;
        if (!ctx.SAMEUPDATELEVEL().isEmpty()) {
            applicationRestriction |= RewriteTaclet.SAME_UPDATE_LEVEL;
        }
        if (!ctx.INSEQUENTSTATE().isEmpty()) {
            applicationRestriction |= RewriteTaclet.IN_SEQUENT_STATE;
        }
        if (!ctx.ANTECEDENTPOLARITY().isEmpty()) {
            applicationRestriction |= RewriteTaclet.ANTECEDENT_POLARITY;
        }
        if (!ctx.SUCCEDENTPOLARITY().isEmpty()) {
            applicationRestriction |= RewriteTaclet.SUCCEDENT_POLARITY;
        }
        @Nullable
        Object find = accept(ctx.find);
        TacletBuilder<?> b = createTacletBuilderFor(find, applicationRestriction, ctx);
        currentTBuilder.push(b);
        b.setIfSequent(ifSeq);
        b.setName(new Name(name));
        accept(ctx.goalspecs());
        mapOf(ctx.varexplist());
        accept(ctx.modifiers());
        b.setChoices(choices);
        b.setAnnotations(tacletAnnotations);
        b.setOrigin(BuilderHelpers.getPosition(ctx));
        try {
            Taclet r = peekTBuilder().getTaclet();
            registerTaclet(ctx, r);
            setSchemaVariables(schemaVariables().parent());
            currentTBuilder.pop();
            return r;
        } catch (RuntimeException e) {
            throw new BuildingException(ctx, e);
        }
    }

    private void registerTaclet(KeYParser.Datatype_declContext ctx, TacletBuilder<?> tb) {
        var taclet = tb.getTaclet();
        taclet2Builder.put(taclet, peekTBuilder());
        topLevelTaclets.add(taclet);
        LOGGER.trace("Taclet announced: \"{}\" from {}:{}", taclet.name(),
            ctx.start.getTokenSource().getSourceName(), ctx.start.getLine());
    }

    private void registerTaclet(ParserRuleContext ctx, Taclet taclet) {
        taclet2Builder.put(taclet, peekTBuilder());
        LOGGER.trace("Taclet announced: \"{}\" from {}:{}", taclet.name(),
            ctx.start.getTokenSource().getSourceName(), ctx.start.getLine());
    }

    private TacletBuilder<?> peekTBuilder() {
        return currentTBuilder.peek();
    }


    @Override
    public Object visitDatatype_decl(KeYParser.Datatype_declContext ctx) {
        var tbAx = createAxiomTaclet(ctx);
        registerTaclet(ctx, tbAx);

        var tbInd = createInductionTaclet(ctx);
        registerTaclet(ctx, tbInd);

        var tbSplit = createConstructorSplit(ctx);
        registerTaclet(ctx, tbSplit);

        Sort dtSort = namespaces().sorts().lookup(ctx.name.getText());
        for (var constructor : ctx.datatype_constructor()) {
            for (int i = 0; i < constructor.sortId().size(); i++) {
                var argName = constructor.argName.get(i).getText();

                var tbDeconstructor = createDeconstructorTaclet(constructor, argName, i);
                registerTaclet(ctx, tbDeconstructor);

                var tbDeconsEq = createDeconstructorEQTaclet(constructor, argName, i, dtSort);
                registerTaclet(ctx, tbDeconsEq);
            }
        }

        return null;
    }

    private TacletBuilder<? extends Taclet> createDeconstructorTaclet(
            KeYParser.Datatype_constructorContext constructor, String argName, int argIndex) {
        var tacletBuilder = new RewriteTacletBuilder<>();
        tacletBuilder
                .setName(new Name(String.format("%s_Dec_%s", argName, constructor.name.getText())));
        tacletBuilder.setDisplayName(
            String.format("%s_Deconstruct_%s", argName, constructor.name.getText()));

        var schemaVariables = new OperatorSV[constructor.argName.size()];
        var args = new Term[constructor.argName.size()];
        var tb = services.getTermBuilder();

        // Schema vars for constructor, e.g., Cons(head_sv, tail_sv)
        for (int i = 0; i < constructor.argName.size(); i++) {
            var name = constructor.argName.get(i).getText() + "_sv";
            Sort sort = accept(constructor.argSort.get(i));
            var sv = declareSchemaVariable(constructor, name, sort, false, false, false,
                new SchemaVariableModifierSet.TermSV());
            schemaVariables[i] = sv;
            args[i] = tb.var(sv);
        }

        var function = namespaces().functions().lookup(argName);
        var consFn = namespaces().functions().lookup(constructor.name.getText());

        // Find, e.g, tail(Cons(head_sv, tail_sv))
        tacletBuilder.setFind(tb.func(function, tb.func(consFn, args)));
        tacletBuilder.addTacletGoalTemplate(
            new RewriteTacletGoalTemplate(tb.var(schemaVariables[argIndex])));
        tacletBuilder.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);

        return tacletBuilder;
    }

    private TacletBuilder<? extends Taclet> createDeconstructorEQTaclet(
            KeYParser.Datatype_constructorContext constructor, String argName, int argIndex,
            Sort dtSort) {
        var tacletBuilder = new RewriteTacletBuilder<>();
        tacletBuilder.setName(
            new Name(String.format("%s_DecEQ_%s", argName, constructor.name.getText())));
        tacletBuilder.setDisplayName(
            String.format("%s_DeconstructEQ_%s", argName, constructor.name.getText()));

        var schemaVariables = new OperatorSV[constructor.argName.size()];
        var args = new Term[constructor.argName.size()];
        var tb = services.getTermBuilder();

        // Schema vars for constructor, e.g., Cons(head_sv, tail_sv)
        for (int i = 0; i < constructor.argName.size(); i++) {
            var name = constructor.argName.get(i).getText() + "_sv";
            Sort sort = accept(constructor.argSort.get(i));
            var sv = declareSchemaVariable(constructor, name, sort, false, false, false,
                new SchemaVariableModifierSet.TermSV());
            schemaVariables[i] = sv;
            args[i] = tb.var(sv);
        }

        var function = namespaces().functions().lookup(argName);
        var consFn = namespaces().functions().lookup(constructor.name.getText());

        var x = declareSchemaVariable(constructor, argName + "_x", dtSort, false, false, false,
            new SchemaVariableModifierSet.TermSV());
        var res = schemaVariables[argIndex];

        tacletBuilder.setFind(tb.func(function, tb.var(x)));
        tacletBuilder.setIfSequent(Sequent.createAnteSequent(
            new Semisequent(new SequentFormula(tb.equals(tb.var(x), tb.func(consFn, args))))));
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(tb.var(res)));
        tacletBuilder.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);

        return tacletBuilder;
    }


    private TacletBuilder<? extends Taclet> createInductionTaclet(
            KeYParser.Datatype_declContext ctx) {
        var tacletBuilder = new NoFindTacletBuilder();
        tacletBuilder.setName(new Name(String.format("%s_Ind", ctx.name.getText())));
        final var sort = sorts().lookup(ctx.name.getText());
        var phi = declareSchemaVariable(ctx, "phi", JavaDLTheory.FORMULA, true,
            false, false, new SchemaVariableModifierSet.FormulaSV());
        var tb = services.getTermBuilder();
        var qvar = (VariableSV) declareSchemaVariable(ctx, "x", sort,
            true, false, false,
            new SchemaVariableModifierSet.VariableSV());
        // tacletBuilder.addVarsNotFreeIn(qvar, phi);

        var cases = ctx.datatype_constructor().stream()
                .map(it -> createGoalDtConstructor(it, qvar, tb.var(phi), sort))
                .collect(Collectors.toList());

        var use = tb.all(qvar, tb.var(phi));
        var useCase = new TacletGoalTemplate(
            Sequent.createAnteSequent(new Semisequent(new SequentFormula(use))),
            ImmutableSLList.nil());
        useCase.setName("Use case of " + ctx.name.getText());
        cases.add(useCase);

        cases.forEach(tacletBuilder::addTacletGoalTemplate);
        tacletBuilder.setDisplayName("Induction_for_" + sort.name());
        return tacletBuilder;
    }

    private TacletGoalTemplate createGoalDtConstructor(KeYParser.Datatype_constructorContext it,
            VariableSV qvar, Term var, Sort sort) {
        var constr = createQuantifiedFormula(it, qvar, var, sort);
        var goal = new TacletGoalTemplate(
            Sequent.createSuccSequent(new Semisequent(new SequentFormula(constr))),
            ImmutableSLList.nil());
        goal.setName(it.getText());
        return goal;
    }


    private TacletBuilder<NoFindTaclet> createAxiomTaclet(
            KeYParser.Datatype_declContext ctx) {
        var tacletBuilder = new NoFindTacletBuilder();
        tacletBuilder.setName(new Name(String.format("%s_Axiom", ctx.name.getText())));
        final var sort = sorts().lookup(ctx.name.getText());
        var phi = declareSchemaVariable(ctx, "phi", JavaDLTheory.FORMULA, true,
            false, false, new SchemaVariableModifierSet.FormulaSV());
        var tb = services.getTermBuilder();
        var qvar = (VariableSV) declareSchemaVariable(ctx, "x", sort,
            true, false, false,
            new SchemaVariableModifierSet.VariableSV());
        var find = tb.all(qvar, tb.var(phi)); // \forall #x #phi

        var cases = ctx.datatype_constructor().stream()
                .map(it -> createQuantifiedFormula(it, qvar, tb.var(phi), sort))
                .collect(Collectors.toList());

        var axiom = tb.equals(find, tb.and(cases));

        var goal = new TacletGoalTemplate(
            Sequent.createAnteSequent(new Semisequent(new SequentFormula(axiom))),
            ImmutableSLList.nil());
        tacletBuilder.addTacletGoalTemplate(goal);

        tacletBuilder.setDisplayName("Axiom_for_" + sort.name());
        return tacletBuilder;
    }

    private Term createQuantifiedFormula(KeYParser.Datatype_constructorContext context,
            QuantifiableVariable qvX, Term phi, Sort dt) {
        var tb = services.getTermBuilder();
        var fn = functions().lookup(context.name.getText());
        if (context.argName.isEmpty())
            return tb.subst(qvX, tb.func(fn), phi);

        var args = new Term[context.argName.size()];

        var argSort =
            context.argSort.stream()
                    .map(it -> sorts().lookup(it.getText()))
                    .toList();
        var argNames =
            context.argName.stream()
                    .map(RuleContext::getText)
                    .toList();
        var qvs = new ArrayList<QuantifiableVariable>(args.length);
        var ind = new ArrayList<Term>(args.length);

        for (int i = 0; i < argSort.size(); i++) {
            final var qv = new LogicVariable(new Name(argNames.get(i)), argSort.get(i));
            qvs.add(qv);
            args[i] = services.getTermFactory().createTerm(qvs.get(i));

            if (argSort.get(i).equals(dt)) {
                ind.add(tb.subst(qvX, args[i], phi));
            }
        }

        if (ind.isEmpty()) {
            return tb.all(qvs, tb.func(fn, args));
        } else {
            var base = tb.and(ind);
            return tb.all(qvs, tb.imp(base, tb.subst(qvX, tb.func(fn, args), phi)));
        }
    }

    private RewriteTacletBuilder<RewriteTaclet> createConstructorSplit(
            KeYParser.Datatype_declContext ctx) {
        final var tb = services.getTermBuilder();

        final String prefix = ctx.name.getText() + "_";

        Map<String, Term> variables = new HashMap<>();
        for (KeYParser.Datatype_constructorContext context : ctx.datatype_constructor()) {
            for (int i = 0; i < context.argName.size(); i++) {
                var name = context.argName.get(i).getText();
                var sort = sorts().lookup(context.argSort.get(i).getText());
                var sv = declareSchemaVariable(ctx, prefix + name, sort,
                    false, true, false,
                    new SchemaVariableModifierSet.TermSV());
                variables.put(name, tb.var(sv));
            }
        }

        final var b = new RewriteTacletBuilder<>();
        b.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
        final var sort = sorts().lookup(ctx.name.getText());

        b.setName(new Name(sort.name() + "_ctor_split"));
        b.setDisplayName("case distinction of " + sort.name());

        var phi = declareSchemaVariable(ctx, "var", sort,
            false, false, false,
            new SchemaVariableModifierSet.TermSV());
        b.setFind(tb.var(phi));
        for (KeYParser.Datatype_constructorContext context : ctx.datatype_constructor()) {
            var func = functions().lookup(context.name.getText());
            Term[] args = new Term[context.argName.size()];
            for (int i = 0; i < args.length; i++) {
                args[i] = variables.get(context.argName.get(i).getText());
            }
            Semisequent antec =
                new Semisequent(new SequentFormula(tb.equals(tb.var(phi), tb.func(func, args))));
            Sequent addedSeq = Sequent.createAnteSequent(antec);
            TacletGoalTemplate goal = new TacletGoalTemplate(addedSeq, ImmutableSLList.nil());
            goal.setName("#var = " + context.name.getText());
            b.addTacletGoalTemplate(goal);
        }
        return b;
    }

    @Override
    public Object visitModifiers(KeYParser.ModifiersContext ctx) {
        TacletBuilder<?> b = peekTBuilder();
        List<RuleSet> rs = accept(ctx.rs);
        if (!ctx.NONINTERACTIVE().isEmpty()) {
            b.addRuleSet(ruleSets().lookup(new Name("notHumanReadable")));
        }

        if (rs != null) {
            rs.forEach(b::addRuleSet);
        }

        if (ctx.DISPLAYNAME() != null) {// last entry
            b.setDisplayName(accept(ctx.dname));
        }

        if (ctx.HELPTEXT() != null) { // last entry
            b.setHelpText(accept(ctx.htext));
        }

        mapOf(ctx.triggers());
        return null;
    }

    @Override
    public Object visitVarexplist(KeYParser.VarexplistContext ctx) {
        return mapOf(ctx.varexp());
    }

    @Override
    public Object visitVarexp(KeYParser.VarexpContext ctx) {
        boolean negated = ctx.NOT_() != null;
        String name = ctx.varexpId().getText();
        List<KeYParser.Varexp_argumentContext> arguments = ctx.varexp_argument();
        List<TacletBuilderCommand> suitableManipulators =
            TacletBuilderManipulators.getConditionBuildersFor(name);
        List<String> parameters =
            ctx.parameter.stream().map(Token::getText).collect(Collectors.toList());
        boolean applied = false;
        Object[] argCache = new Object[arguments.size()];
        for (TacletBuilderCommand manipulator : suitableManipulators) {
            if (applyManipulator(negated, argCache, manipulator, arguments, parameters)) {
                applied = true;
                break;
            }
        }
        if (!applied) {
            LOGGER.warn("Found name-matching conditions with following type signature:");
            suitableManipulators.forEach(it -> LOGGER.warn(Arrays.toString(it.getArgumentTypes())));
            LOGGER.warn("But you gave {} arguments.\n", arguments.size());
            semanticError(ctx, "Could not apply the given variable condition: %s", ctx.getText());
        }
        return null;
    }

    private boolean applyManipulator(boolean negated, Object[] args,
            TacletBuilderCommand manipulator, List<KeYParser.Varexp_argumentContext> arguments,
            List<String> parameters) {
        assert args.length == arguments.size();
        ArgumentType[] types = manipulator.getArgumentTypes();

        if (types.length != arguments.size()) {
            return false;
        }
        try {
            for (int i = 0; i < arguments.size(); i++) {
                args[i] = evaluateVarcondArgument(types[i], args[i], arguments.get(i));
            }
            manipulator.apply(peekTBuilder(), args, parameters, negated);
            return true;
        } catch (Throwable e) {
            return false;
        }
    }

    private Object evaluateVarcondArgument(ArgumentType expectedType, Object prevValue,
            KeYParser.Varexp_argumentContext ctx) {
        if (prevValue != null && expectedType.clazz.isAssignableFrom(prevValue.getClass())) {
            return prevValue; // previous value is of suitable type, we do not re-evaluate
        }

        return switch (expectedType) {
        case TYPE_RESOLVER -> buildTypeResolver(ctx);
        case SORT -> visitSortId(ctx.term().getText(), ctx.term());
        case JAVA_TYPE -> getOrCreateJavaType(ctx.term().getText(), ctx);
        case VARIABLE -> varId(ctx, ctx.getText());
        case STRING -> ctx.getText();
        case TERM -> accept(ctx.term());
        };
    }

    private Sort visitSortId(String text, ParserRuleContext ctx) {
        String primitiveName = text;
        Type t = null;
        if (primitiveName.equals(PrimitiveType.JAVA_BYTE.getName())) {
            t = PrimitiveType.JAVA_BYTE;
            primitiveName = PrimitiveType.JAVA_INT.getName();
        } else if (primitiveName.equals(PrimitiveType.JAVA_CHAR.getName())) {
            t = PrimitiveType.JAVA_CHAR;
            primitiveName = PrimitiveType.JAVA_INT.getName();
        } else if (primitiveName.equals(PrimitiveType.JAVA_SHORT.getName())) {
            t = PrimitiveType.JAVA_SHORT;
            primitiveName = PrimitiveType.JAVA_INT.getName();
        } else if (primitiveName.equals(PrimitiveType.JAVA_INT.getName())) {
            t = PrimitiveType.JAVA_INT;
            primitiveName = PrimitiveType.JAVA_INT.getName();
        } else if (primitiveName.equals(PrimitiveType.JAVA_LONG.getName())) {
            t = PrimitiveType.JAVA_LONG;
            primitiveName = PrimitiveType.JAVA_INT.getName();
        } else if (primitiveName.equals(PrimitiveType.JAVA_BIGINT.getName())) {
            t = PrimitiveType.JAVA_BIGINT;
            primitiveName = PrimitiveType.JAVA_BIGINT.getName();
        }
        Sort s = lookupSort(primitiveName);
        if (s == null) {
            semanticError(ctx, "Could not find sort: %s", text);
        }

        if (text.contains("[")) {
            var num = text.indexOf('[') - text.lastIndexOf(']') / 2 + 1;
            return toArraySort(new Pair<>(s, t), num);
        }
        return s;
    }

    private KeYJavaType getOrCreateJavaType(String sortId, ParserRuleContext ctx) {
        KeYJavaType t = getJavaInfo().getKeYJavaType(sortId);
        if (t != null) {
            return t;
        }
        return new KeYJavaType(visitSortId(sortId, ctx));
    }


    public Object buildTypeResolver(KeYParser.Varexp_argumentContext ctx) {
        SchemaVariable y = accept(ctx.varId());
        if (ctx.TYPEOF() != null) {
            return TypeResolver.createElementTypeResolver(y);
        }
        if (ctx.CONTAINERTYPE() != null) {
            return TypeResolver.createContainerTypeResolver(y);
        }

        Sort s = visitSortId(ctx.term().getText(), ctx.term());
        if (s != null) {
            if (s instanceof GenericSort) {
                return TypeResolver.createGenericSortResolver((GenericSort) s);
            } else {
                return TypeResolver.createNonGenericSortResolver(s);
            }
        }
        return null;
    }

    @Override
    public Object visitGoalspecs(KeYParser.GoalspecsContext ctx) {
        return mapOf(ctx.goalspecwithoption());
    }

    @Override
    public Object visitGoalspecwithoption(KeYParser.GoalspecwithoptionContext ctx) {
        ChoiceExpr expr = accept(ctx.option_list());
        goalChoice = expr == null ? ChoiceExpr.TRUE : expr;
        accept(ctx.goalspec());
        return null;
    }

    @Override
    public Choice visitOption(KeYParser.OptionContext ctx) {
        String choice = ctx.getText();
        Choice c = choices().lookup(choice);
        if (c == null) {
            semanticError(ctx, "Could not find choice: %s", choice);
        }
        return c;
    }

    @Override
    public ChoiceExpr visitOption_list(KeYParser.Option_listContext ctx) {
        return ctx.option_expr().stream()
                .map(it -> (ChoiceExpr) accept(it))
                .reduce(ChoiceExpr::and)
                .orElse(ChoiceExpr.TRUE);
    }

    @Override
    public ChoiceExpr visitOption_expr_or(KeYParser.Option_expr_orContext ctx) {
        return ChoiceExpr.or(accept(ctx.option_expr(0)), accept(ctx.option_expr(1)));
    }

    @Override
    public ChoiceExpr visitOption_expr_paren(KeYParser.Option_expr_parenContext ctx) {
        return accept(ctx.option_expr());
    }

    @Override
    public ChoiceExpr visitOption_expr_prop(KeYParser.Option_expr_propContext ctx) {
        String category = ctx.option().cat.getText();
        String value = ctx.option().value.getText();
        String choiceStr = category + ":" + value;
        /*
         * Make sure that the choice (category and value!) is known to KeY, i.e. that it is declared
         * in the file `optionsDeclarations.key`. This prevents from accidentally deactivating
         * (parts of) taclets due to non-existing choices (see
         * https://github.com/KeYProject/key/issues/3352).
         */
        if (choices().lookup(choiceStr) == null) {
            semanticError(ctx, "Could not find choice: %s", category + ":" + choiceStr);
        }
        return ChoiceExpr.variable(ctx.option().cat.getText(), ctx.option().value.getText());
    }

    @Override
    public ChoiceExpr visitOption_expr_not(KeYParser.Option_expr_notContext ctx) {
        return ChoiceExpr.not(accept(ctx.option_expr()));
    }

    @Override
    public ChoiceExpr visitOption_expr_and(KeYParser.Option_expr_andContext ctx) {
        return ChoiceExpr.and(accept(ctx.option_expr(0)), accept(ctx.option_expr(1)));
    }

    @Override
    public Object visitGoalspec(KeYParser.GoalspecContext ctx) {
        var soc = this.goalChoice;
        String name = accept(ctx.string_value());

        Sequent addSeq = Sequent.EMPTY_SEQUENT;
        ImmutableSLList<Taclet> addRList = ImmutableSLList.nil();
        DefaultImmutableSet<SchemaVariable> addpv = DefaultImmutableSet.nil();

        @Nullable
        Object rwObj = accept(ctx.replacewith());
        if (ctx.add() != null) {
            addSeq = accept(ctx.add());
        }
        if (ctx.addrules() != null) {
            addRList = accept(ctx.addrules()); // modifies goalChoice
        }
        if (ctx.addprogvar() != null) {
            addpv = accept(ctx.addprogvar());
        }
        addGoalTemplate(name, rwObj, addSeq, addRList, addpv, soc, ctx);
        return null;
    }

    @Override
    public Object visitReplacewith(KeYParser.ReplacewithContext ctx) {
        return accept(ctx.o);
    }

    @Override
    public Object visitAdd(KeYParser.AddContext ctx) {
        return accept(ctx.s);
    }

    @Override
    public Object visitAddrules(KeYParser.AddrulesContext ctx) {
        return accept(ctx.lor);
    }

    @Override
    public ImmutableSet<SchemaVariable> visitAddprogvar(KeYParser.AddprogvarContext ctx) {
        final Collection<? extends SchemaVariable> accept = accept(ctx.pvs);
        return Immutables.<SchemaVariable>createSetFrom(Objects.requireNonNull(accept));
    }

    @Override
    public ImmutableList<Taclet> visitTacletlist(KeYParser.TacletlistContext ctx) {
        List<Taclet> taclets = mapOf(ctx.taclet());
        return ImmutableList.fromList(taclets);
    }

    private @NonNull TacletBuilder<?> createTacletBuilderFor(Object find,
            int applicationRestriction,
            ParserRuleContext ctx) {
        if (find == null) {
            return new NoFindTacletBuilder();
        } else if (find instanceof Term) {
            return new RewriteTacletBuilder<>().setFind((Term) find)
                    .setApplicationRestriction(applicationRestriction);
        } else if (find instanceof Sequent findSeq) {
            if (findSeq.isEmpty()) {
                return new NoFindTacletBuilder();
            } else if (findSeq.antecedent().size() == 1 && findSeq.succedent().isEmpty()) {
                Term findFma = findSeq.antecedent().get(0).formula();
                AntecTacletBuilder b = new AntecTacletBuilder();
                b.setFind(findFma);
                b.setIgnoreTopLevelUpdates(
                    (applicationRestriction & RewriteTaclet.IN_SEQUENT_STATE) == 0);
                return b;
            } else if (findSeq.antecedent().isEmpty() && findSeq.succedent().size() == 1) {
                Term findFma = findSeq.succedent().get(0).formula();
                SuccTacletBuilder b = new SuccTacletBuilder();
                b.setFind(findFma);
                b.setIgnoreTopLevelUpdates(
                    (applicationRestriction & RewriteTaclet.IN_SEQUENT_STATE) == 0);
                return b;
            } else {
                semanticError(ctx, "Unknown find-sequent (perhaps null?):" + findSeq);
            }
        } else {
            semanticError(ctx, "Unknown find class type: %s", find.getClass().getName());
        }

        throw new IllegalArgumentException(
            format("Could not find a suitable TacletBuilder for {0}", find));
    }

    private void addGoalTemplate(String id, Object rwObj, Sequent addSeq,
            ImmutableList<Taclet> addRList, ImmutableSet<SchemaVariable> pvs,
            @Nullable ChoiceExpr soc, ParserRuleContext ctx) {
        TacletBuilder<?> b = peekTBuilder();
        TacletGoalTemplate gt = null;
        if (rwObj == null) {
            // there is no replacewith, so we take
            gt = new TacletGoalTemplate(addSeq, addRList, pvs);
        } else {
            if (b instanceof NoFindTacletBuilder) {
                // there is a replacewith without a find.
                throwEx(new RecognitionException(""));
            } else if (b instanceof SuccTacletBuilder || b instanceof AntecTacletBuilder) {
                if (rwObj instanceof Sequent) {
                    gt = new AntecSuccTacletGoalTemplate(addSeq, addRList, (Sequent) rwObj, pvs);
                } else {
                    semanticError(ctx, // new UnfittingReplacewithException
                        "Replacewith in a Antec-or SuccTaclet has to contain a sequent (not a term)");

                }
            } else if (b instanceof RewriteTacletBuilder) {
                if (rwObj instanceof Term) {
                    gt = new RewriteTacletGoalTemplate(addSeq, addRList, (Term) rwObj, pvs);
                } else {
                    // throwEx(/new UnfittingReplacewithException
                    semanticError(ctx,
                        "Replacewith in a RewriteTaclet has to contain a term (not a sequent)");
                }
            }
        }
        if (gt == null) {
            throw new NullPointerException(
                "Could not find a suitable goal template builder for: " + b.getClass());
        }
        gt.setName(id);
        b.addTacletGoalTemplate(gt);
        if (soc != null) {
            b.addGoal2ChoicesMapping(gt, soc);
        }
    }

    @Override
    public SchemaVariable visitVarId(KeYParser.VarIdContext ctx) {
        String id = ctx.id.getText();
        return varId(ctx, id);
    }

    private @Nullable SchemaVariable varId(ParserRuleContext ctx, String id) {
        Name name = new Name(id);
        SchemaVariable v = schemaVariables().lookup(name);
        if (v == null) {
            semanticError(ctx, "Could not find Variable %s", id);
        }
        return v;
    }

    @Override
    public Object visitOne_schema_var_decl(KeYParser.One_schema_var_declContext ctx) {
        boolean makeVariableSV = false;
        boolean makeSkolemTermSV = false;
        boolean makeTermLabelSV = false;
        SchemaVariableModifierSet mods = null;
        accept(ctx.one_schema_modal_op_decl());
        Sort s = null;
        List<String> ids = accept(ctx.simple_ident_comma_list());
        if (ctx.PROGRAM() != null) {
            mods = new SchemaVariableModifierSet.ProgramSV();
            accept(ctx.schema_modifiers(), mods);
            String id = accept(ctx.id);
            String nameString = accept(ctx.nameString);
            String parameter = accept(ctx.simple_ident_dots());
            if (nameString != null && !"name".equals(nameString)) {
                semanticError(ctx, "Unrecognized token '%s', expected 'name'", nameString);
            }
            ProgramSVSort psv = ProgramSVSort.name2sort().get(new Name(id));
            s = parameter != null ? psv.createInstance(parameter) : psv;
            if (s == null) {
                semanticError(ctx, "Program SchemaVariable of type '%s' not found.", id);
            }
        }
        if (ctx.FORMULA() != null) {
            mods = new SchemaVariableModifierSet.FormulaSV();
            accept(ctx.schema_modifiers(), mods);
            s = JavaDLTheory.FORMULA;
        }
        if (ctx.TERMLABEL() != null) {
            makeTermLabelSV = true;
            mods = new SchemaVariableModifierSet.TermLabelSV();
            accept(ctx.schema_modifiers(), mods);
        }
        if (ctx.UPDATE() != null) {
            mods = new SchemaVariableModifierSet.FormulaSV();
            accept(ctx.schema_modifiers(), mods);
            s = JavaDLTheory.UPDATE;
        }
        if (ctx.SKOLEMFORMULA() != null) {
            makeSkolemTermSV = true;
            mods = new SchemaVariableModifierSet.FormulaSV();
            accept(ctx.schema_modifiers(), mods);
            s = JavaDLTheory.FORMULA;
        }
        if (ctx.TERM() != null) {
            mods = new SchemaVariableModifierSet.TermSV();
            accept(ctx.schema_modifiers(), mods);
        }
        if (ctx.VARIABLE() != null || ctx.VARIABLES() != null) {
            makeVariableSV = true;
            mods = new SchemaVariableModifierSet.VariableSV();
            accept(ctx.schema_modifiers(), mods);
        }
        if (ctx.SKOLEMTERM() != null) {
            makeSkolemTermSV = true;
            mods = new SchemaVariableModifierSet.SkolemTermSV();
            accept(ctx.schema_modifiers(), mods);
        }

        if (ctx.MODALOPERATOR() != null) {
            accept(ctx.one_schema_modal_op_decl());
            return null;
        }

        if (ctx.sortId() != null) {
            s = accept(ctx.sortId());
        }

        for (String id : Objects.requireNonNull(ids)) {
            declareSchemaVariable(ctx, id, s, makeVariableSV, makeSkolemTermSV, makeTermLabelSV,
                mods);
        }
        return null;
    }

    @Override
    public Object visitSchema_modifiers(KeYParser.Schema_modifiersContext ctx) {
        SchemaVariableModifierSet mods = pop();
        List<String> ids = visitSimple_ident_comma_list(ctx.simple_ident_comma_list());
        for (String id : ids) {
            if (!mods.addModifier(id)) {
                semanticError(ctx,
                    "Illegal or unknown modifier in declaration of schema variable: %s", id);
            }
        }
        return null;
    }

    @Override
    public Object visitSchema_var_decls(KeYParser.Schema_var_declsContext ctx) {
        return this.<SchemaVariable>mapOf(ctx.one_schema_var_decl());
    }

    protected OperatorSV declareSchemaVariable(ParserRuleContext ctx, String name, Sort s,
            boolean makeVariableSV, boolean makeSkolemTermSV, boolean makeTermLabelSV,
            SchemaVariableModifierSet mods) {
        OperatorSV v;
        if (s == JavaDLTheory.FORMULA && !makeSkolemTermSV) {
            v = SchemaVariableFactory.createFormulaSV(new Name(name), mods.rigid());
        } else if (s == JavaDLTheory.UPDATE) {
            v = SchemaVariableFactory.createUpdateSV(new Name(name));
        } else if (s instanceof ProgramSVSort) {
            v = SchemaVariableFactory.createProgramSV(new ProgramElementName(name),
                (ProgramSVSort) s, mods.list());
        } else {
            if (makeVariableSV) {
                v = SchemaVariableFactory.createVariableSV(new Name(name), s);
            } else if (makeSkolemTermSV) {
                v = SchemaVariableFactory.createSkolemTermSV(new Name(name), s);
            } else if (makeTermLabelSV) {
                v = SchemaVariableFactory.createTermLabelSV(new Name(name));
            } else {
                v = SchemaVariableFactory.createTermSV(new Name(name), s, mods.rigid(),
                    mods.strict());
            }
        }

        if (variables().lookup(v.name()) != null) {
            semanticError(null, "Schema variables shadows previous declared variable: %s.",
                v.name());
        }

        if (schemaVariables().lookup(v.name()) != null) {
            OperatorSV old = (OperatorSV) schemaVariables().lookup(v.name());
            if (!old.sort().equals(v.sort())) {
                semanticError(null,
                    "Schema variables clashes with previous declared schema variable: %s.",
                    v.name());
            }
            LOGGER.error("Override: {} {}", old, v);
        }
        schemaVariables().add(v);
        return v;
    }

    public List<Taclet> getTopLevelTaclets() {
        return topLevelTaclets;
    }
}
