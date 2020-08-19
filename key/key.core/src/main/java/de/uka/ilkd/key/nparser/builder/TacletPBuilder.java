package de.uka.ilkd.key.nparser.builder;

import antlr.RecognitionException;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.varexp.ArgumentType;
import de.uka.ilkd.key.nparser.varexp.TacletBuilderCommand;
import de.uka.ilkd.key.nparser.varexp.TacletBuilderManipulators;
import de.uka.ilkd.key.parser.SchemaVariableModifierSet;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.conditions.TypeResolver;
import de.uka.ilkd.key.rule.tacletbuilder.*;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.jetbrains.annotations.Nullable;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import java.util.*;
import java.util.stream.Collectors;

public class TacletPBuilder extends ExpressionBuilder {

    private final Stack<TacletBuilder<?>> currentTBuilder = new Stack<>();

    private HashMap<Taclet, TacletBuilder<? extends Taclet>> taclet2Builder = new HashMap<>();

    private boolean axiomMode;

    private final List<Taclet> topLevelTaclets = new ArrayList<>(2048);

    /**
     * Current required choices for taclets
     */
    private ImmutableSet<Choice> requiredChoices = DefaultImmutableSet.nil();

    /**
     * Required choices for taclet goals.
     */
    private ImmutableSet<Choice> goalChoice = DefaultImmutableSet.nil();

    public TacletPBuilder(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    public TacletPBuilder(Services services, NamespaceSet namespaces, HashMap<Taclet, TacletBuilder<? extends Taclet>> taclet2Builder) {
        this(services, namespaces);
        this.taclet2Builder = taclet2Builder;
    }

    @Override
    public Object visitDecls(KeYParser.DeclsContext ctx) {
        mapOf(ctx.schema_var_decls());
        mapOf(ctx.rulesOrAxioms());
        return null;
    }

    @Override
    public Object visitRulesOrAxioms(KeYParser.RulesOrAxiomsContext ctx) {
        enableJavaSchemaMode();
        if (ctx.RULES() != null) axiomMode = false;
        if (ctx.AXIOMS() != null) axiomMode = true;
        List<Choice> choices = accept(ctx.choices);
        if (choices != null) {
            this.requiredChoices = ImmutableSet.fromCollection(choices);
        } else {
            this.requiredChoices = DefaultImmutableSet.nil();
        }
        List<Taclet> seq = mapOf(ctx.taclet());
        topLevelTaclets.addAll(seq);
        /* no check for conflicts: Check should happen after options
        for (Taclet s : seq) {
            if (s == null) continue; //TODO investigate why null taclets appear!
            final RuleKey key = new RuleKey(s);
            /*if (topLevelTaclets.containsKey(key)) {
                semanticError(ctx, "Cannot add taclet \"" + s.name() +
                        "\" to rule base as a taclet with the same " +
                        "name already exists.");

            } else {
            }
        }*/
        disableJavaSchemaMode();
        return null;
    }

    @Override
    public Object visitOne_schema_modal_op_decl(KeYParser.One_schema_modal_op_declContext ctx) {
        ImmutableSet<Modality> modalities = DefaultImmutableSet.nil();
        Sort sort = accept(ctx.sort);
        if (sort != null && sort != Sort.FORMULA) {
            semanticError(ctx, "Modal operator SV must be a FORMULA, not " + sort);
        }
        List<String> ids = accept(ctx.simple_ident_comma_list());
        String id = accept(ctx.simple_ident());

        for (String s : ids) {
            modalities = opSVHelper(s, modalities);
        }
        SchemaVariable osv = schemaVariables().lookup(new Name(id));
        /*if (osv != null) {
            //semanticError("Schema variable " + id + " already defined.");
            //System.err.format("Clash with %s\n", osv);
        }*/

        osv = SchemaVariableFactory.createModalOperatorSV(new Name(id), sort, modalities);
        schemaVariables().add(osv);
        return osv;
    }

    @Override
    public TacletBuilder visitTriggers(KeYParser.TriggersContext ctx) {
        String id = (String) ctx.id.accept(this);
        SchemaVariable triggerVar = schemaVariables().lookup(new Name(id));
        if (triggerVar == null) {
            semanticError(ctx, "Undeclared schemavariable: " + id);
        }
        TacletBuilder b = peekTBuilder();
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
        List<Choice> ch = accept(ctx.option_list());
        ImmutableSet<Choice> choices = requiredChoices;
        if (ch != null) {
            choices = choices.add(ch);
        }

        Term form = accept(ctx.form);
        if (form != null) {
            if (!axiomMode) {
                semanticError(ctx, "formula rules are only permitted for \\axioms");
            }
            TacletBuilder b = createTacletBuilderFor(null, RewriteTaclet.NONE, ctx);
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
            announceTaclet(ctx, r);
            currentTBuilder.pop();
            return r;
        }

        //  schema var decls
        setSchemaVariables(new Namespace<>(schemaVariables()));
        mapOf(ctx.one_schema_var_decl());

        if (ctx.ifSeq != null) ifSeq = accept(ctx.ifSeq);

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
        @Nullable Object find = accept(ctx.find);
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
            announceTaclet(ctx, r);
            setSchemaVariables(schemaVariables().parent());
            currentTBuilder.pop();
            return r;
        } catch (RuntimeException e) {
            //new BuildingException(e).printStackTrace();
            throw new BuildingException(ctx, e);
        }
    }

    private void announceTaclet(ParserRuleContext ctx, Taclet taclet) {
        taclet2Builder.put(taclet, peekTBuilder());
        /*
        if (currentTBuilder.size() > 1) {//toplevel taclet
            return;
        }
        if (parsedKeyFile.getTaclets().containsKey(key)) {
            //semanticError(ctx, "A taclet with name %s was already defined", key);
            System.err.format("Taclet clash with %s%n", key);
        }*/
        //System.out.format("ANNOUNCE: %s @ %s:%d%n", key, ctx.start.getTokenSource().getSourceName(), ctx.start.getLine());
        //parsedKeyFile.getTaclets().put(key, taclet);
    }

    private TacletBuilder<?> peekTBuilder() {
        return currentTBuilder.peek();
    }


    @Override
    public Object visitModifiers(KeYParser.ModifiersContext ctx) {
        TacletBuilder b = peekTBuilder();
        List<RuleSet> rs = accept(ctx.rs);
        if (!ctx.NONINTERACTIVE().isEmpty()) {
            b.addRuleSet(ruleSets().lookup(new Name("notHumanReadable")));
        }

        if (rs != null) {
            rs.forEach(b::addRuleSet);
        }

        if (ctx.DISPLAYNAME() != null) {//last entry
            b.setDisplayName(accept(ctx.dname));
        }

        if (ctx.HELPTEXT() != null) { //last entry
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
        List<TacletBuilderCommand> suitableManipulators = TacletBuilderManipulators.getConditionBuildersFor(name);
        List<String> parameters = ctx.parameter.stream().map(Token::getText).collect(Collectors.toList());
        boolean applied = false;
        Object[] argCache = new Object[arguments.size()];
        for (TacletBuilderCommand manipulator : suitableManipulators) {
            if (applyManipulator(negated, argCache, manipulator, arguments, parameters)) {
                applied = true;
                break;
            }
        }
        if (!applied) {
            System.err.println("Found name-matching conditions with following type signature:");
            suitableManipulators.forEach(
                    it -> System.err.println(Arrays.toString(it.getArgumentTypes())));
            System.err.format("But you gave %d arguments.\n", arguments.size());
            semanticError(ctx, "Could not apply the given variable condition: %s", name);
        }
        return null;
    }

    /**
     * @param negated
     * @param args
     * @param manipulator
     * @param arguments
     * @param parameters
     * @return
     */
    private boolean applyManipulator(
            boolean negated,
            Object[] args,
            TacletBuilderCommand manipulator,
            List<KeYParser.Varexp_argumentContext> arguments,
            List<String> parameters) {
        assert args.length == arguments.size();
        ArgumentType[] types = manipulator.getArgumentTypes();

        if (types.length != arguments.size())
            return false;
        try {

            for (int i = 0; i < arguments.size(); i++) {
                args[i] = evaluateVarcondArgument(types[i], args[i], arguments.get(i));
            }

            manipulator.apply(peekTBuilder(), args, parameters, negated);
            return true;
        } catch (Throwable e) {
            e.printStackTrace();
            return false;
        }

    }

    private Object evaluateVarcondArgument(
            ArgumentType expectedType,
            Object prevValue,
            KeYParser.Varexp_argumentContext ctx) {
        if (prevValue != null && expectedType.clazz.isAssignableFrom(prevValue.getClass())) {
            return prevValue; //previous value is of suitable type, we do not re-evaluate
        }

        switch (expectedType) {
            case TYPE_RESOLVER:
                return buildTypeResolver(ctx);
            case SORT:
                return accept(ctx.sortId());
            case JAVA_TYPE:
                return getJavaInfo().getKeYJavaType(ctx.sortId().getText());
            case VARIABLE:
                return varId(ctx, ctx.getText());
            case STRING:
                return ctx.getText();
            case TERM:
                return accept(ctx.term());
        }
        assert false;
        return null;
    }


    public Object buildTypeResolver(KeYParser.Varexp_argumentContext ctx) {
        SchemaVariable y = accept(ctx.varId());
        if (ctx.TYPEOF() != null) {
            return TypeResolver.createElementTypeResolver(y);
        }
        if (ctx.CONTAINERTYPE() != null) {
            return TypeResolver.createContainerTypeResolver(y);
        }

        Sort s = accept(ctx.sortId());
        if (s != null) {
            if (s instanceof GenericSort) {
                return TypeResolver.createGenericSortResolver((GenericSort) s);
            } else {
                return TypeResolver.createNonGenericSortResolver(s);
            }
        }
        return null;
    }

    /*
    @Override
    public Object visitVarcond_sameObserver(KeYParser.Varcond_sameObserverContext ctx) {
        ParsableVariable t1 = accept(ctx.t1);
        ParsableVariable t2 = accept(ctx.t2);
        peekTBuilder().addVariableCondition(new SameObserverCondition(t1, t2));
        return null;
    }

    @Override
    public Object visitVarcond_applyUpdateOnRigid(KeYParser.Varcond_applyUpdateOnRigidContext ctx) {
        var u = accept(ctx.u);
        var x = accept(ctx.x);
        var x2 = accept(ctx.x2);

        peekTBuilder().addVariableCondition(new ApplyUpdateOnRigidCondition((UpdateSV) u,
                (SchemaVariable) x,
                (SchemaVariable) x2));
        return null;
    }

    @Override
    public Object visitVarcond_dropEffectlessElementaries(KeYParser.Varcond_dropEffectlessElementariesContext ctx) {
        UpdateSV u = accept(ctx.u);
        SchemaVariable x = accept(ctx.x);
        SchemaVariable result = accept(ctx.result);

        peekTBuilder().addVariableCondition(new DropEffectlessElementariesCondition(
                u, x, result));
        return null;
    }

    @Override
    public Object visitVarcond_dropEffectlessStores(KeYParser.Varcond_dropEffectlessStoresContext ctx) {
        var h = accept(ctx.h);
        var o = accept(ctx.o);
        var f = accept(ctx.f);
        var x = accept(ctx.x);
        var result = accept(ctx.result);

        peekTBuilder().addVariableCondition(new DropEffectlessStoresCondition((TermSV) h,
                (TermSV) o,
                (TermSV) f,
                (TermSV) x,
                (TermSV) result));
        return null;
    }

    @Override
    public Object visitVarcond_differentFields(KeYParser.Varcond_differentFieldsContext ctx) {
        var x = accept(ctx.x);
        var y = accept(ctx.y);

        peekTBuilder().addVariableCondition(new DifferentFields((SchemaVariable) x, (SchemaVariable) y));
        return null;
    }

    @Override
    public Object visitVarcond_simplifyIfThenElseUpdate(KeYParser.Varcond_simplifyIfThenElseUpdateContext ctx) {
        FormulaSV phi = accept(ctx.phi);
        UpdateSV u1 = accept(ctx.u1);
        UpdateSV u2 = accept(ctx.u2);
        FormulaSV commonFormula = accept(ctx.commonFormula);
        SchemaVariable result = accept(ctx.result);

        peekTBuilder().addVariableCondition(new SimplifyIfThenElseUpdateCondition(phi,
                u1,
                u2,
                commonFormula,
                result));
        return null;
    }



    @Override
    public Object visitVarcond_new(KeYParser.Varcond_newContext ctx) {
        var x = accept(ctx.x);
        var y = accept(ctx.y);

        if (ctx.TYPEOF() != null) {
            peekTBuilder().addVarsNew((SchemaVariable) x, (SchemaVariable) y);
        }

        if (ctx.DEPENDINGON() != null) {
            peekTBuilder().addVarsNewDependingOn((SchemaVariable) x, (SchemaVariable) y);
        }

        if (ctx.kjt != null) {
            KeYJavaType kjt = accept(ctx.kjt);
            peekTBuilder().addVarsNew((SchemaVariable) x, kjt.getJavaType());
        }
        return null;
    }

    @Override
    public Object visitVarcond_newlabel(KeYParser.Varcond_newlabelContext ctx) {
        var x = accept(ctx.x);

        peekTBuilder().addVariableCondition(new NewJumpLabelCondition((SchemaVariable) x));
        return null;
    }

    @Override
    public Object visitVarcond_typecheck(KeYParser.Varcond_typecheckContext ctx) {
        TypeComparisonCondition.Mode mode = null;
        if (ctx.SAME() != null) {
            mode = negated
                    ? TypeComparisonCondition.Mode.NOT_SAME
                    : TypeComparisonCondition.Mode.SAME;
        }
        if (ctx.ISSUBTYPE() != null) {
            mode = negated
                    ? TypeComparisonCondition.Mode.NOT_IS_SUBTYPE
                    : TypeComparisonCondition.Mode.IS_SUBTYPE;
        }
        if (ctx.STRICT() != null) {
            if (negated)
                semanticError(ctx, "A negated strict subtype check does not make sense.");
            mode = TypeComparisonCondition.Mode.STRICT_SUBTYPE;
        }
        if (ctx.DISJOINTMODULONULL() != null) {
            if (negated)
                semanticError(ctx, "Negation not supported");
            mode = TypeComparisonCondition.Mode.DISJOINTMODULONULL;
        }

        TypeResolver fst = accept(ctx.fst);
        TypeResolver snd = accept(ctx.snd);

        peekTBuilder().addVariableCondition(new TypeComparisonCondition(fst, snd, mode));
        return null;
    }

    @Override
    public Object visitVarcond_free(KeYParser.Varcond_freeContext ctx) {
        SchemaVariable x = accept(ctx.x);
        List<SchemaVariable> ys = accept(ctx.varIds());

        ys.forEach(it -> peekTBuilder().addVarsNotFreeIn(x, it));
        return null;
    }

    @Override
    public Object visitVarcond_hassort(KeYParser.Varcond_hassortContext ctx) {
        var x = accept(ctx.x);
        var elemSort = ctx.ELEMSORT() != null;
        Sort s = accept(ctx.any_sortId_check());
        if (!(s instanceof GenericSort)) {
            semanticError(ctx, "Generic sort is expected. Got: %s.", s);
        } else if (!JavaTypeToSortCondition.checkSortedSV((SchemaVariable) x)) {
            semanticError(ctx, "Expected schema variable of kind EXPRESSION or TYPE, but is " + x);
        } else {

            peekTBuilder().addVariableCondition(new JavaTypeToSortCondition((SchemaVariable) x,
                    (GenericSort) s,
                    elemSort));
        }
        return null;
    }

    @Override
    public Object visitVarcond_fieldtype(KeYParser.Varcond_fieldtypeContext ctx) {
        var x = accept(ctx.x);
        Sort s = accept(ctx.any_sortId_check());

        if (!(s instanceof GenericSort)) {
            semanticError(ctx, "Generic sort expected. got: %s.", s);
        } else if (!FieldTypeToSortCondition.checkSortedSV((SchemaVariable) x)) {
            semanticError(ctx, "Expected schema variable of kind EXPRESSION or TYPE, "
                    + "but is " + x);
        } else {

            peekTBuilder().addVariableCondition(new FieldTypeToSortCondition((SchemaVariable) x,
                    (GenericSort) s));
        }
        return null;
    }

    @Override
    public Object visitVarcond_containsAssignment(KeYParser.Varcond_containsAssignmentContext ctx) {
        var x = accept(ctx.x);

        peekTBuilder().addVariableCondition(new ContainsAssignmentCondition((SchemaVariable) x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_enumtype(KeYParser.Varcond_enumtypeContext ctx) {
        TypeResolver tr = accept(ctx.tr);

        peekTBuilder().addVariableCondition(new EnumTypeCondition(tr, negated));
        return null;
    }

    @Override
    public Object visitVarcond_reference(KeYParser.Varcond_referenceContext ctx) {
        boolean nonNull = false;
        if (ctx.id != null && "non_null".equals(ctx.id.getText())) {
            nonNull = true;
        } else {
            semanticError(ctx,
                    "%s is not an allowed modifier for the \\isReference variable condition.", ctx.id);
        }
        TypeResolver tr = accept(ctx.tr);

        boolean isPrimitive = false;//TODO check
        peekTBuilder().addVariableCondition(new TypeCondition(tr, !isPrimitive, nonNull));
        return null;
    }

    @Override
    public Object visitVarcond_thisreference(KeYParser.Varcond_thisreferenceContext ctx) {
        String id = null;
        boolean nonNull = false;
        ParsableVariable x = accept(ctx.x);

        peekTBuilder().addVariableCondition(new IsThisReference(x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_staticmethod(KeYParser.Varcond_staticmethodContext ctx) {
        var x = accept(ctx.x);
        var y = accept(ctx.y);
        var z = accept(ctx.z);

        peekTBuilder().addVariableCondition(new StaticMethodCondition
                (negated, (SchemaVariable) x, (SchemaVariable) y, (SchemaVariable) z));
        return null;
    }

    @Override
    public Object visitVarcond_mayexpandmethod(KeYParser.Varcond_mayexpandmethodContext ctx) {
        SchemaVariable x = accept(ctx.x);
        SchemaVariable y = accept(ctx.y);
        SchemaVariable z = accept(ctx.z);

        if (z != null)
            peekTBuilder().addVariableCondition(new MayExpandMethodCondition(
                    negated, x, y, z));
        else
            peekTBuilder().addVariableCondition(new MayExpandMethodCondition(
                    negated, null, x, y));
        return null;
    }

    @Override
    public Object visitVarcond_referencearray(KeYParser.Varcond_referencearrayContext ctx) {
        SchemaVariable x = accept(ctx.x);

        boolean primitiveElementType = false;//TODO check
        peekTBuilder().addVariableCondition(new ArrayComponentTypeCondition(
                x, !primitiveElementType));
        return null;
    }

    @Override
    public Object visitVarcond_array(KeYParser.Varcond_arrayContext ctx) {
        SchemaVariable x = accept(ctx.x);

        peekTBuilder().addVariableCondition(new ArrayTypeCondition(
                x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_array_length(KeYParser.Varcond_array_lengthContext ctx) {
        SchemaVariable x = accept(ctx.x);

        peekTBuilder().addVariableCondition(new ArrayLengthCondition(
                x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_abstractOrInterface(KeYParser.Varcond_abstractOrInterfaceContext ctx) {
        TypeResolver tr = accept(ctx.tr);

        peekTBuilder().addVariableCondition(new AbstractOrInterfaceType(tr, negated));
        return null;
    }

    @Override
    public Object visitVarcond_enum_const(KeYParser.Varcond_enum_constContext ctx) {
        SchemaVariable x = accept(ctx.x);

        peekTBuilder().addVariableCondition(new EnumConstantCondition(
                x));
        return null;
    }

    @Override
    public Object visitVarcond_final(KeYParser.Varcond_finalContext ctx) {
        SchemaVariable x = accept(ctx.x);

        peekTBuilder().addVariableCondition(new FinalReferenceCondition(
                x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_static(KeYParser.Varcond_staticContext ctx) {
        SchemaVariable x = accept(ctx.x);

        peekTBuilder().addVariableCondition(new StaticReferenceCondition(
                x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_localvariable(KeYParser.Varcond_localvariableContext ctx) {
        SchemaVariable x = accept(ctx.x);

        peekTBuilder().addVariableCondition(new LocalVariableCondition(x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_observer(KeYParser.Varcond_observerContext ctx) {
        TermSV obs = accept(ctx.obs);
        TermSV heap = accept(ctx.heap);


        peekTBuilder().addVariableCondition(new ObserverCondition(obs,
                heap));
        return null;
    }

    @Override
    public Object visitVarcond_different(KeYParser.Varcond_differentContext ctx) {
        SchemaVariable var1 = accept(ctx.var1);
        SchemaVariable var2 = accept(ctx.var2);

        peekTBuilder().addVariableCondition(new DifferentInstantiationCondition(
                var1,
                var2));
        return null;
    }

    @Override
    public Object visitVarcond_metadisjoint(KeYParser.Varcond_metadisjointContext ctx) {
        var var1 = accept(ctx.var1);
        var var2 = accept(ctx.var2);

        peekTBuilder().addVariableCondition(new MetaDisjointCondition(
                (TermSV) var1,
                (TermSV) var2));
        return null;
    }

    @Override
    public Object visitVarcond_equalUnique(KeYParser.Varcond_equalUniqueContext ctx) {
        var t = accept(ctx.t);
        var t2 = accept(ctx.t2);
        var phi = accept(ctx.phi);

        peekTBuilder().addVariableCondition(new EqualUniqueCondition((TermSV) t,
                (TermSV) t2,
                (FormulaSV) phi));
        return null;
    }

    @Override
    public Object visitVarcond_freeLabelIn(KeYParser.Varcond_freeLabelInContext ctx) {
        var l = accept(ctx.l);
        var statement = accept(ctx.statement);

        peekTBuilder().addVariableCondition(new FreeLabelInVariableCondition((SchemaVariable) l,
                (SchemaVariable) statement, negated));
        return null;
    }

    @Override
    public Object visitVarcond_constant(KeYParser.Varcond_constantContext ctx) {
        var x = accept(ctx.varId());

        if (x instanceof TermSV) {
            peekTBuilder().addVariableCondition(new ConstantCondition((TermSV) x, negated));
        } else {
            assert x instanceof FormulaSV;
            peekTBuilder().addVariableCondition(new ConstantCondition((FormulaSV) x, negated));
        }
        return null;
    }


    /*
    @Override
    public Object visitVarcond_label(KeYParser.Varcond_labelContext ctx) {
        TermLabelSV l = accept(ctx.varId());
        String name = accept(ctx.simple_ident());

        peekTBuilder().addVariableCondition(new TermLabelCondition(l, name, negated));
        return null;
    }

    @Override
    public Object visitVarcond_static_field(KeYParser.Varcond_static_fieldContext ctx) {
        var field = accept(ctx.varId());

        peekTBuilder().addVariableCondition(new StaticFieldCondition((SchemaVariable) field, negated));
        return null;
    }

    @Override
    public Object visitVarcond_subFormulas(KeYParser.Varcond_subFormulasContext ctx) {
        FormulaSV x = accept(ctx.varId());
        peekTBuilder().addVariableCondition(new SubFormulaCondition(x, negated));
        return null;
    }
    */

    @Override
    public Object visitGoalspecs(KeYParser.GoalspecsContext ctx) {
        return mapOf(ctx.goalspecwithoption());
    }

    @Override
    public Object visitGoalspecwithoption(KeYParser.GoalspecwithoptionContext ctx) {
        List<Choice> s = accept(ctx.option_list());
        goalChoice = s == null ? DefaultImmutableSet.nil() : ImmutableSet.fromCollection(s);
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
    public List<Choice> visitOption_list(KeYParser.Option_listContext ctx) {
        return mapOf(ctx.option());
    }

    @Override
    public Object visitGoalspec(KeYParser.GoalspecContext ctx) {
        ImmutableSet<Choice> soc = this.goalChoice;
        String name = accept(ctx.string_value());

        Sequent addSeq = Sequent.EMPTY_SEQUENT;
        ImmutableSLList<Taclet> addRList = ImmutableSLList.<Taclet>nil();
        DefaultImmutableSet<SchemaVariable> addpv = DefaultImmutableSet.<SchemaVariable>nil();

        @Nullable Object rwObj = accept(ctx.replacewith());
        if (ctx.add() != null) addSeq = accept(ctx.add());
        if (ctx.addrules() != null) addRList = accept(ctx.addrules()); //modifies goalChoice
        if (ctx.addprogvar() != null) addpv = accept(ctx.addprogvar());
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
        return ImmutableSet.fromSet(new HashSet<>(accept(ctx.pvs)));
    }

    @Override
    public ImmutableList<Taclet> visitTacletlist(KeYParser.TacletlistContext ctx) {
        List<Taclet> taclets = mapOf(ctx.taclet());
        return ImmutableList.fromList(taclets);
    }

    /*private boolean isTermTransformer()  {
        return (input.LA(1) == KeYLexer.IDENT &&
                AbstractTermTransformer.name2metaop(input.LT(1).getText()) != null)
                || input.LA(1) == KeYLexer.IN_TYPE;
    }
    */


    private TacletBuilder<?> createTacletBuilderFor(Object find, int applicationRestriction, ParserRuleContext ctx) {
        if (applicationRestriction != RewriteTaclet.NONE &&
                applicationRestriction != RewriteTaclet.IN_SEQUENT_STATE &&
                !(find instanceof Term)) {
            String mod = "";
            if ((applicationRestriction & RewriteTaclet.SAME_UPDATE_LEVEL) != 0) {
                mod = "\"\\sameUpdateLevel\"";
            }
            if ((applicationRestriction & RewriteTaclet.ANTECEDENT_POLARITY) != 0) {
                if (mod != "") mod += " and ";
                mod += "\"\\antecedentPolarity\"";
            }
            if ((applicationRestriction & RewriteTaclet.SUCCEDENT_POLARITY) != 0) {
                if (mod != "") mod += " and ";
                mod += "\"\\succedentPolarity\"";
            }
            if (mod == "") {
                mod = "Application restrictions";
            }
        }
        if (find == null) {
            return new NoFindTacletBuilder();
        } else if (find instanceof Term) {
            return new RewriteTacletBuilder().setFind((Term) find)
                    .setApplicationRestriction(applicationRestriction);
        } else if (find instanceof Sequent) {
            Sequent findSeq = (Sequent) find;
            if (findSeq.isEmpty()) {
                return new NoFindTacletBuilder();
            } else if (findSeq.antecedent().size() == 1
                    && findSeq.succedent().size() == 0) {
                Term findFma = findSeq.antecedent().get(0).formula();
                AntecTacletBuilder b = new AntecTacletBuilder();
                b.setFind(findFma);
                b.setIgnoreTopLevelUpdates((applicationRestriction & RewriteTaclet.IN_SEQUENT_STATE) == 0);
                return b;
            } else if (findSeq.antecedent().size() == 0
                    && findSeq.succedent().size() == 1) {
                Term findFma = findSeq.succedent().get(0).formula();
                SuccTacletBuilder b = new SuccTacletBuilder();
                b.setFind(findFma);
                b.setIgnoreTopLevelUpdates((applicationRestriction & RewriteTaclet.IN_SEQUENT_STATE) == 0);
                return b;
            } else {
                semanticError(ctx, "Unknown find-sequent (perhaps null?):" + findSeq);
            }
        } else {
            semanticError(ctx, "Unknown find class type: %s", find.getClass().getName());
        }
        return null;
    }

    private void addGoalTemplate(String id,
                                 Object rwObj,
                                 Sequent addSeq,
                                 ImmutableList<Taclet> addRList,
                                 ImmutableSet<SchemaVariable> pvs,
                                 @Nullable ImmutableSet<Choice> soc,
                                 ParserRuleContext ctx) {
        TacletBuilder<?> b = peekTBuilder();
        TacletGoalTemplate gt = null;
        if (rwObj == null) {
            // there is no replacewith, so we take
            gt = new TacletGoalTemplate(addSeq, addRList, pvs);
        } else {
            if (b instanceof NoFindTacletBuilder) {
                // there is a replacewith without a find.
                throwEx(new RecognitionException(""));
            } else if (b instanceof SuccTacletBuilder
                    || b instanceof AntecTacletBuilder) {
                if (rwObj instanceof Sequent) {
                    gt = new AntecSuccTacletGoalTemplate(addSeq,
                            addRList,
                            (Sequent) rwObj,
                            pvs);
                } else {
                    semanticError(ctx, //new UnfittingReplacewithException
                            "Replacewith in a Antec-or SuccTaclet has to contain a sequent (not a term)");

                }
            } else if (b instanceof RewriteTacletBuilder) {
                if (rwObj instanceof Term) {
                    gt = new RewriteTacletGoalTemplate(addSeq,
                            addRList,
                            (Term) rwObj,
                            pvs);
                } else {
                    //throwEx(/new UnfittingReplacewithException
                    semanticError(ctx, "Replacewith in a RewriteTaclet has to contain a term (not a sequent)");
                }
            }
        }
        if (gt == null)
            throw new NullPointerException("Could not find a suitable goal template builder for: " + b.getClass());
        gt.setName(id);
        b.addTacletGoalTemplate(gt);
        if (soc != null) b.addGoal2ChoicesMapping(gt, soc);
    }

    @Override
    public Operator visitVarId(KeYParser.VarIdContext ctx) {
        String id = ctx.id.getText();
        return varId(ctx, id);
    }

    @Nullable
    private Operator varId(ParserRuleContext ctx, String id) {
        Name name = new Name(id);
        Operator v = variables().lookup(name);
        if (v == null) {
            v = schemaVariables().lookup(name);
        }
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
            //List<String> ids = accept(ctx.simple_ident_comma_list());
            //TODO?
        }
        if (ctx.FORMULA() != null) {
            mods = new SchemaVariableModifierSet.FormulaSV();
            accept(ctx.schema_modifiers(), mods);
            s = Sort.FORMULA;
        }
        if (ctx.TERMLABEL() != null) {
            makeTermLabelSV = true;
            mods = new SchemaVariableModifierSet.TermLabelSV();
            accept(ctx.schema_modifiers(), mods);
        }
        if (ctx.UPDATE() != null) {
            mods = new SchemaVariableModifierSet.FormulaSV();
            accept(ctx.schema_modifiers(), mods);
            s = Sort.UPDATE;
        }
        if (ctx.SKOLEMFORMULA() != null) {
            makeSkolemTermSV = true;
            mods = new SchemaVariableModifierSet.FormulaSV();
            accept(ctx.schema_modifiers(), mods);
            s = Sort.FORMULA;
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

        if (ctx.sortId() != null)
            s = accept(ctx.sortId());

        for (String id : ids) {
            declareSchemaVariable(ctx, id,
                    s, makeVariableSV, makeSkolemTermSV,
                    makeTermLabelSV, mods);
        }
        return null;
    }

    @Override
    public Object visitSchema_modifiers(KeYParser.Schema_modifiersContext ctx) {
        SchemaVariableModifierSet mods = pop();
        List<String> ids = visitSimple_ident_comma_list(ctx.simple_ident_comma_list());
        for (String id : ids) {
            if (!mods.addModifier(id))
                semanticError(ctx, "Illegal or unknown modifier in declaration of schema variable: %s", id);
        }
        return null;
    }

    @Override
    public Object visitSchema_var_decls(KeYParser.Schema_var_declsContext ctx) {
        return this.<SchemaVariable>mapOf(ctx.one_schema_var_decl());
    }

    protected void declareSchemaVariable(
            ParserRuleContext ctx,
            String name, Sort s,
            boolean makeVariableSV, boolean makeSkolemTermSV, boolean makeTermLabelSV,
            SchemaVariableModifierSet mods) {
        SchemaVariable v;
        if (s == Sort.FORMULA && !makeSkolemTermSV) {
            v = SchemaVariableFactory.createFormulaSV(new Name(name),
                    mods.rigid());
        } else if (s == Sort.UPDATE) {
            v = SchemaVariableFactory.createUpdateSV(new Name(name));
        } else if (s instanceof ProgramSVSort) {
            v = SchemaVariableFactory.createProgramSV(
                    new ProgramElementName(name),
                    (ProgramSVSort) s,
                    mods.list());
        } else {
            if (makeVariableSV) {
                v = SchemaVariableFactory.createVariableSV
                        (new Name(name), s);
            } else if (makeSkolemTermSV) {
                v = SchemaVariableFactory.createSkolemTermSV(new Name(name),
                        s);
            } else if (makeTermLabelSV) {
                v = SchemaVariableFactory.createTermLabelSV(new Name(name));
            } else {
                v = SchemaVariableFactory.createTermSV(
                        new Name(name),
                        s, mods.rigid(), mods.strict());
            }
        }

        if (variables().lookup(v.name()) != null) {
            semanticError(null, "Schema variables shadows previous declared variable: %s.", v.name());
        }

        if (schemaVariables().lookup(v.name()) != null) {
            SchemaVariable old = schemaVariables().lookup(v.name());
            if (!old.sort().equals(v.sort()))
                semanticError(null,
                        "Schema variables clashes with previous declared schema variable: %s.", v.name());
            System.err.format("Override: %s %s%n", old, v);
        }
        schemaVariables().add(v);
    }

    public List<Taclet> getTopLevelTaclets() {
        return topLevelTaclets;
    }
}
