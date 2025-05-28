/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.builder;


import java.util.*;
import java.util.stream.Collectors;

import org.key_project.logic.*;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.rules.Taclet;
import org.key_project.prover.rules.TacletAnnotation;
import org.key_project.prover.rules.Trigger;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.abstraction.KeYRustyType;
import org.key_project.rusty.ast.abstraction.PrimitiveType;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.logic.*;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.sv.OperatorSV;
import org.key_project.rusty.logic.op.sv.SchemaVariableFactory;
import org.key_project.rusty.logic.sort.ProgramSVSort;
import org.key_project.rusty.parser.KeYRustyParser;
import org.key_project.rusty.parser.SchemaVariableModifierSet;
import org.key_project.rusty.parser.varcond.ArgumentType;
import org.key_project.rusty.parser.varcond.TacletBuilderCommand;
import org.key_project.rusty.parser.varcond.TacletBuilderManipulators;
import org.key_project.rusty.proof.calculus.RustySequentKit;
import org.key_project.rusty.rule.*;
import org.key_project.rusty.rule.tacletbuilder.*;
import org.key_project.rusty.util.parsing.BuildingException;
import org.key_project.util.collection.*;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

import static java.text.MessageFormat.format;

public class TacletPBuilder extends ExpressionBuilder {
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

    // --------------------------
    // Constructors
    // --------------------------

    public TacletPBuilder(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    public TacletPBuilder(Services services, NamespaceSet nss,
            Map<Taclet, TacletBuilder<? extends Taclet>> taclet2Builder) {
        this(services, nss);
        this.taclet2Builder = taclet2Builder;
    }

    // --------------------------
    // Methods
    // --------------------------

    @Override
    public Object visitDecls(KeYRustyParser.DeclsContext ctx) {
        mapOf(ctx.schema_var_decls());
        mapOf(ctx.rulesOrAxioms());
        mapOf(ctx.datatype_decls());
        return null;
    }

    @Override
    public Object visitRulesOrAxioms(KeYRustyParser.RulesOrAxiomsContext ctx) {
        enableRustySchemaMode();
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
    public Object visitOne_schema_modal_op_decl(
            KeYRustyParser.One_schema_modal_op_declContext ctx) {
        ImmutableSet<Modality.RustyModalityKind> modalities = DefaultImmutableSet.nil();
        Sort sort = accept(ctx.sort);
        if (sort != null && sort != RustyDLTheory.FORMULA) {
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
    public TacletBuilder<?> visitTriggers(KeYRustyParser.TriggersContext ctx) {
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
    public Taclet visitTaclet(KeYRustyParser.TacletContext ctx) {
        Sequent ifSeq = RustySequentKit.getInstance().getEmptySequent();
        ImmutableSet<TacletAnnotation> tacletAnnotations = DefaultImmutableSet.nil();
        if (ctx.LEMMA() != null) {
            tacletAnnotations = tacletAnnotations.add(TacletAnnotation.LEMMA);
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
            TacletBuilder<?> b =
                createTacletBuilderFor(null, Taclet.ApplicationRestriction.NONE, ctx);
            currentTBuilder.push(b);
            Sequent addSeq = RustySequentKit
                    .createAnteSequent(ImmutableSLList.singleton(new SequentFormula(form)));
            ImmutableList<Taclet> noTaclets = ImmutableSLList.nil();
            DefaultImmutableSet<SchemaVariable> noSV = DefaultImmutableSet.nil();
            addGoalTemplate(null, null, addSeq, noTaclets, noSV, null, ctx);
            b.setName(new Name(name));
            b.setChoices(choices);
            b.setAnnotations(tacletAnnotations);
            // b.setOrigin(BuilderHelpers.getPosition(ctx));
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

        @Nullable
        Object find = accept(ctx.find);
        Sequent seq = find instanceof Sequent ? (Sequent) find : null;

        var applicationRestriction = Taclet.ApplicationRestriction.NONE;
        if (!ctx.SAMEUPDATELEVEL().isEmpty()) {
            applicationRestriction =
                applicationRestriction.combine(Taclet.ApplicationRestriction.SAME_UPDATE_LEVEL);
        }
        if (!ctx.INSEQUENTSTATE().isEmpty()) {
            applicationRestriction =
                applicationRestriction.combine(Taclet.ApplicationRestriction.IN_SEQUENT_STATE);
        }
        if (!ctx.ANTECEDENTPOLARITY().isEmpty() || (seq != null && !seq.antecedent().isEmpty())) {
            applicationRestriction =
                applicationRestriction.combine(Taclet.ApplicationRestriction.ANTECEDENT_POLARITY);
        }
        if (!ctx.SUCCEDENTPOLARITY().isEmpty() || (seq != null && !seq.succedent().isEmpty())) {
            applicationRestriction =
                applicationRestriction.combine(Taclet.ApplicationRestriction.SUCCEDENT_POLARITY);
        }

        TacletBuilder<?> b = createTacletBuilderFor(find, applicationRestriction, ctx);
        currentTBuilder.push(b);
        b.setIfSequent(ifSeq);
        b.setName(new Name(name));
        accept(ctx.goalspecs());
        mapOf(ctx.varexplist());
        accept(ctx.modifiers());
        b.setChoices(choices);
        b.setAnnotations(tacletAnnotations);
        // b.setOrigin(BuilderHelpers.getPosition(ctx));
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

    private void registerTaclet(KeYRustyParser.Datatype_declContext ctx, TacletBuilder<?> tb) {
        var taclet = tb.getTaclet();
        taclet2Builder.put(taclet, peekTBuilder());
        topLevelTaclets.add(taclet);
    }

    private void registerTaclet(ParserRuleContext ctx, Taclet taclet) {
        taclet2Builder.put(taclet, peekTBuilder());
    }

    private TacletBuilder<?> peekTBuilder() {
        return currentTBuilder.peek();
    }

    // @Override
    // public Object visitDatatype_decl(KeYRustyParser.Datatype_declContext ctx) {
    // var tbAx = createAxiomTaclet(ctx);
    // registerTaclet(ctx, tbAx);
    //
    // var tbInd = createInductionTaclet(ctx);
    // registerTaclet(ctx, tbInd);
    //
    // var tbSplit = createConstructorSplit(ctx);
    // registerTaclet(ctx, tbSplit);
    //
    // Sort dtSort = namespaces().sorts().lookup(ctx.name.getText());
    // for (var constructor : ctx.datatype_constructor()) {
    // for (int i = 0; i < constructor.sortId().size(); i++) {
    // var argName = constructor.argName.get(i).getText();
    //
    // var tbDeconstructor = createDeconstructorTaclet(constructor, argName, i);
    // registerTaclet(ctx, tbDeconstructor);
    //
    // var tbDeconsEq = createDeconstructorEQTaclet(constructor, argName, i, dtSort);
    // registerTaclet(ctx, tbDeconsEq);
    // }
    // }
    //
    // return null;
    // }

    // ------------------------------------------------------------------------------------------
    // here we skip everything from createDeconstructorTaclet(...) to createConstructorSplit(...)
    // ------------------------------------------------------------------------------------------


    @Override
    public Object visitModifiers(KeYRustyParser.ModifiersContext ctx) {
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

        // if (ctx.HELPTEXT() != null) { // last entry
        // b.setHelpText(accept(ctx.htext));
        // }

        mapOf(ctx.triggers());
        return null;
    }

    @Override
    public Object visitVarexplist(KeYRustyParser.VarexplistContext ctx) {
        return mapOf(ctx.varexp());
    }

    @Override
    public Object visitVarexp(KeYRustyParser.VarexpContext ctx) {
        boolean negated = ctx.NOT_() != null;
        String name = ctx.varexpId().getText();
        List<KeYRustyParser.Varexp_argumentContext> arguments = ctx.varexp_argument();
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
            semanticError(ctx, "Could not apply the given variable condition: %s", ctx.getText());
        }
        return null;
    }

    private boolean applyManipulator(boolean negated, Object[] args,
            TacletBuilderCommand manipulator, List<KeYRustyParser.Varexp_argumentContext> arguments,
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
            KeYRustyParser.Varexp_argumentContext ctx) {
        if (prevValue != null && expectedType.clazz.isAssignableFrom(prevValue.getClass())) {
            return prevValue; // previous value is of suitable type, we do not re-evaluate
        }

        return switch (expectedType) {
        // case TYPE_RESOLVER -> buildTypeResolver(ctx);
        case SORT -> visitSortId(ctx.term().getText(), ctx.term());
        case RUST_TYPE -> getOrCreateRustyType(ctx.term().getText(), ctx);
        case VARIABLE -> varId(ctx, ctx.getText());
        case STRING -> ctx.getText();
        case TERM -> accept(ctx.term());
        };
    }

    private Sort visitSortId(String text, ParserRuleContext ctx) {
        String primitiveName = text;
        Type t = null;
        if (primitiveName.equals(PrimitiveType.U8.name().toString())
                || primitiveName.equals(PrimitiveType.U16.name().toString())
                || primitiveName.equals(PrimitiveType.U32.name().toString())
                || primitiveName.equals(PrimitiveType.U64.name().toString())
                || primitiveName.equals(PrimitiveType.U128.name().toString())
                || primitiveName.equals(PrimitiveType.USIZE.name().toString())
                || primitiveName.equals(PrimitiveType.I8.name().toString())
                || primitiveName.equals(PrimitiveType.I16.name().toString())
                || primitiveName.equals(PrimitiveType.I32.name().toString())
                || primitiveName.equals(PrimitiveType.I64.name().toString())
                || primitiveName.equals(PrimitiveType.I128.name().toString())
                || primitiveName.equals(PrimitiveType.ISIZE.name().toString())) {
            primitiveName = "int";
        }
        Sort s = lookupSort(primitiveName);
        if (s == null) {
            semanticError(ctx, "Could not find sort: %s", text);
        }

        return s;
    }

    private KeYRustyType getOrCreateRustyType(String sortId, ParserRuleContext ctx) {
        KeYRustyType t = services.getRustInfo().getKeYRustyType(sortId);
        if (t != null) {
            return t;
        }

        return new KeYRustyType(visitSortId(sortId, ctx));
    }


    // ---------------------------------------------------------------------------
    // Here we leave out methods from visitSortId(...) to buildTypeResolver(...)
    // ---------------------------------------------------------------------------

    @Override
    public Object visitGoalspecs(KeYRustyParser.GoalspecsContext ctx) {
        return mapOf(ctx.goalspecwithoption());
    }

    @Override
    public Object visitGoalspecwithoption(KeYRustyParser.GoalspecwithoptionContext ctx) {
        ChoiceExpr expr = accept(ctx.option_list());
        goalChoice = expr == null ? ChoiceExpr.TRUE : expr;
        accept(ctx.goalspec());
        return null;
    }

    @Override
    public Choice visitOption(KeYRustyParser.OptionContext ctx) {
        String choice = ctx.getText();
        Choice c = choices().lookup(choice);
        if (c == null) {
            semanticError(ctx, "Could not find choice: %s", choice);
        }
        return c;
    }

    @Override
    public ChoiceExpr visitOption_list(KeYRustyParser.Option_listContext ctx) {
        return ctx.option_expr().stream()
                .map(it -> (ChoiceExpr) accept(it))
                .reduce(ChoiceExpr::and)
                .orElse(ChoiceExpr.TRUE);
    }

    @Override
    public ChoiceExpr visitOption_expr_or(KeYRustyParser.Option_expr_orContext ctx) {
        return ChoiceExpr.or(accept(ctx.option_expr(0)), accept(ctx.option_expr(1)));
    }

    @Override
    public ChoiceExpr visitOption_expr_paren(KeYRustyParser.Option_expr_parenContext ctx) {
        return accept(ctx.option_expr());
    }

    @Override
    public ChoiceExpr visitOption_expr_prop(KeYRustyParser.Option_expr_propContext ctx) {
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
            semanticError(ctx, "Could not find choice: %s", choiceStr);
        }
        return ChoiceExpr.variable(ctx.option().cat.getText(), ctx.option().value.getText());
    }

    @Override
    public ChoiceExpr visitOption_expr_not(KeYRustyParser.Option_expr_notContext ctx) {
        return ChoiceExpr.not(accept(ctx.option_expr()));
    }

    @Override
    public ChoiceExpr visitOption_expr_and(KeYRustyParser.Option_expr_andContext ctx) {
        return ChoiceExpr.and(accept(ctx.option_expr(0)), accept(ctx.option_expr(1)));
    }

    @Override
    public Object visitGoalspec(KeYRustyParser.GoalspecContext ctx) {
        var soc = this.goalChoice;
        String name = accept(ctx.string_value());

        Sequent addSeq = RustySequentKit.getInstance().getEmptySequent();
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
    public Object visitReplacewith(KeYRustyParser.ReplacewithContext ctx) {
        return accept(ctx.o);
    }

    @Override
    public Object visitAdd(KeYRustyParser.AddContext ctx) {
        return accept(ctx.s);
    }

    @Override
    public Object visitAddrules(KeYRustyParser.AddrulesContext ctx) {
        return accept(ctx.lor);
    }

    @Override
    public ImmutableSet<SchemaVariable> visitAddprogvar(KeYRustyParser.AddprogvarContext ctx) {
        final Collection<? extends SchemaVariable> accept = accept(ctx.pvs);
        return Immutables.createSetFrom(Objects.requireNonNull(accept));
    }

    @Override
    public ImmutableList<Taclet> visitTacletlist(KeYRustyParser.TacletlistContext ctx) {
        List<Taclet> taclets = mapOf(ctx.taclet());
        return ImmutableList.fromList(taclets);
    }

    private @NonNull TacletBuilder<?> createTacletBuilderFor(Object find,
            RewriteTaclet.ApplicationRestriction applicationRestriction, ParserRuleContext ctx) {
        if (find == null) {
            return new NoFindTacletBuilder();
        } else if (find instanceof Term) {
            return new RewriteTacletBuilder<>().setFind((Term) find)
                    .setApplicationRestriction(applicationRestriction);
        } else if (find instanceof Sequent findSeq) {
            if (findSeq.isEmpty()) {
                return new NoFindTacletBuilder();
            } else if (findSeq.antecedent().size() == 1 && findSeq.succedent().isEmpty()) {
                AntecTacletBuilder b = new AntecTacletBuilder();
                b.setFind(findSeq);
                b.setApplicationRestriction(applicationRestriction);
                return b;
            } else if (findSeq.antecedent().isEmpty() && findSeq.succedent().size() == 1) {
                SuccTacletBuilder b = new SuccTacletBuilder();
                b.setFind(findSeq);
                b.setApplicationRestriction(applicationRestriction);
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
            @Nullable ChoiceExpr soc,
            ParserRuleContext ctx) {
        TacletBuilder<?> b = peekTBuilder();
        TacletGoalTemplate gt = null;
        if (rwObj == null) {
            // there is no replacewith, so we take
            gt = new TacletGoalTemplate(addSeq, addRList, pvs);
        } else {
            if (b instanceof NoFindTacletBuilder) {
                // there is a replacewith without a find.
                // TODO ask what Exception to throw here
                // throwEx(new RecognitionException(""));
                throw new RuntimeException("TODO what is a RecognitionException used for");
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
    public SchemaVariable visitVarId(KeYRustyParser.VarIdContext ctx) {
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

    // TODO RESUME HERE

    @Override
    public Object visitOne_schema_var_decl(KeYRustyParser.One_schema_var_declContext ctx) {
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
        // TODO ask: Do we also need SchemaVariableModifiers?
        if (ctx.FORMULA() != null) {
            mods = new SchemaVariableModifierSet.FormulaSV();
            accept(ctx.schema_modifiers(), mods);
            s = RustyDLTheory.FORMULA;
        }
        if (ctx.TERMLABEL() != null) {
            makeTermLabelSV = true;
            mods = new SchemaVariableModifierSet.TermLabelSV();
            accept(ctx.schema_modifiers(), mods);
        }
        if (ctx.UPDATE() != null) {
            mods = new SchemaVariableModifierSet.FormulaSV();
            accept(ctx.schema_modifiers(), mods);
            s = RustyDLTheory.UPDATE;
        }
        if (ctx.SKOLEMFORMULA() != null) {
            makeSkolemTermSV = true;
            mods = new SchemaVariableModifierSet.FormulaSV();
            accept(ctx.schema_modifiers(), mods);
            s = RustyDLTheory.FORMULA;
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
    public Object visitSchema_modifiers(KeYRustyParser.Schema_modifiersContext ctx) {
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
    public Object visitSchema_var_decls(KeYRustyParser.Schema_var_declsContext ctx) {
        return this.<SchemaVariable>mapOf(ctx.one_schema_var_decl());
    }

    protected OperatorSV declareSchemaVariable(ParserRuleContext ctx, String name, Sort s,
            boolean makeVariableSV, boolean makeSkolemTermSV, boolean makeTermLabelSV,
            SchemaVariableModifierSet mods) {
        OperatorSV v;
        if (s == RustyDLTheory.FORMULA && !makeSkolemTermSV) {
            v = SchemaVariableFactory.createFormulaSV(new Name(name), mods.rigid());
        } else if (s == RustyDLTheory.UPDATE) {
            v = SchemaVariableFactory.createUpdateSV(new Name(name));
        } else if (s instanceof ProgramSVSort) {
            v = SchemaVariableFactory.createProgramSV(new Name(name),
                (ProgramSVSort) s, mods.list());
        } else {
            if (makeVariableSV) {
                v = SchemaVariableFactory.createVariableSV(new Name(name), s);
            } else if (makeSkolemTermSV) {
                v = SchemaVariableFactory.createSkolemTermSV(new Name(name), s);
                // } else if (makeTermLabelSV) {
                // v = SchemaVariableFactory.createTermLabelSV(new Name(name));
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
        }
        schemaVariables().add(v);
        return v;
    }


    public List<Taclet> getTopLevelTaclets() {
        return topLevelTaclets;
    }
}
