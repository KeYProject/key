package de.uka.ilkd.key.nparser;

import antlr.RecognitionException;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.AmbigiousDeclException;
import de.uka.ilkd.key.parser.SchemaVariableModifierSet;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.conditions.*;
import de.uka.ilkd.key.rule.tacletbuilder.*;
import org.antlr.v4.runtime.ParserRuleContext;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import java.util.*;

public class TacletPBuilder extends ExpressionBuilder {
    private boolean axiomMode;
    private boolean negated = false;
    private boolean isPrimitive;
    private List<Taclet> taclets = new ArrayList<>(2048);
    private boolean primitiveElementType;

    public TacletPBuilder(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    @Override
    public Object visitRulesOrAxioms(KeYParser.RulesOrAxiomsContext ctx) {
        if (ctx.RULES() != null) axiomMode = false;
        if (ctx.AXIOMS() != null) axiomMode = true;
        List<Taclet> seq = allOf(ctx.taclet());
        Map<RuleKey, Taclet> taclets = new HashMap<>();
        for (Taclet s : seq) {
            final RuleKey key = new RuleKey(s);
            if (taclets.containsKey(key)) {
                semanticError(ctx, "Cannot add taclet \"" + s.name() +
                        "\" to rule base as a taclet with the same " +
                        "name already exists.");

            } else {
                taclets.put(key, s);
            }
        }
        return null;
    }


    @Override
    public Object visitOne_schema_modal_op_decl(KeYParser.One_schema_modal_op_declContext ctx) {
        ImmutableSet<Modality> modalities = DefaultImmutableSet.nil();
        Sort sort = accept(ctx.any_sortId_check());
        if (sort != null && sort != Sort.FORMULA) {
            semanticError(ctx, "Modal operator SV must be a FORMULA, not " + sort);
        }
        List<String> ids = accept(ctx.simple_ident_comma_list());
        String id = accept(ctx.simple_ident());

        for (String s : ids) {
            modalities = opSVHelper(s, modalities);
        }
        SchemaVariable osv = schemaVariables().lookup(new Name(id));
        if (osv != null) {
            //semanticError("Schema variable " + id + " already defined.");
            System.err.format("Clash with %s\n", osv);
        }

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
        Term t = accept(ctx.t);
        List<Term> avoidConditions = new ArrayList<>(ctx.term().size());//TODO avoidCond.
        //b.setTrigger(new Trigger(triggerVar, t, avoidConditions));
        return null;
    }

    @Override
    public Taclet visitTaclet(KeYParser.TacletContext ctx) {
        var ifSeq = Sequent.EMPTY_SEQUENT;
        ImmutableSet<TacletAnnotation> tacletAnnotations = DefaultImmutableSet.nil();
        if (ctx.LEMMA() != null) {
            tacletAnnotations = tacletAnnotations.add(de.uka.ilkd.key.rule.TacletAnnotation.LEMMA);
        }
        var name = ctx.name.getText();
        List<Choice> ch = accept(ctx.option_list());
        ImmutableSet<Choice> choices_ = ch == null ? ImmutableSet.empty() : DefaultImmutableSet.fromCollection(ch);

        Term form = accept(ctx.form);
        if (form != null) {
            if (!axiomMode) {
                semanticError(ctx, "formula rules are only permitted for \\axioms");
            }
            TacletBuilder<?> b = createTacletBuilderFor(null, RewriteTaclet.NONE, ctx);
            SequentFormula sform = new SequentFormula(form);
            Semisequent semi = new Semisequent(sform);
            Sequent addSeq = Sequent.createAnteSequent(semi);
            ImmutableList<Taclet> noTaclets = ImmutableSLList.nil();
            DefaultImmutableSet<SchemaVariable> noSV = DefaultImmutableSet.nil();
            addGoalTemplate(b, null, null, addSeq, noTaclets, noSV, null, ctx);
            b.setName(new Name(name));
            b.setChoices(choices_);
            b.setAnnotations(tacletAnnotations);
            Taclet r = b.getTaclet();
            r.setTacletOptions(activatedChoices);
            r.setOrigin(ctx.name.getTokenSource().getSourceName() + ":" + ctx.name.getLine());
            announceTaclet(ctx, r);
            return r;
        }

        //  schema var decls
        schemaVariablesNamespace = new Namespace(schemaVariables());
        allOf(ctx.one_schema_var_decl());

        if (ctx.ifSeq != null) ifSeq = accept(ctx.ifSeq);

        int applicationRestriction = RewriteTaclet.NONE;
        if (null != ctx.SAMEUPDATELEVEL()) {
            applicationRestriction |= RewriteTaclet.SAME_UPDATE_LEVEL;
        }
        if (null != ctx.INSEQUENTSTATE()) {
            applicationRestriction |= RewriteTaclet.IN_SEQUENT_STATE;
        }
        if (null != ctx.ANTECEDENTPOLARITY()) {
            applicationRestriction |= RewriteTaclet.ANTECEDENT_POLARITY;
        }
        if (null != ctx.SUCCEDENTPOLARITY()) {
            applicationRestriction |= RewriteTaclet.SUCCEDENT_POLARITY;
        }
        var find = accept(ctx.find);
        TacletBuilder b = createTacletBuilderFor(find, applicationRestriction, ctx);
        b.setIfSequent(ifSeq);
        b.setName(new Name(name));
        accept(ctx.goalspecs(), b);
        accept(ctx.varexplist(), b);
        accept(ctx.modifiers(), b);
        b.setChoices(choices_);
        b.setAnnotations(tacletAnnotations);
        Taclet r = b.getTaclet();
        r.setTacletOptions(activatedChoices);
        r.setOrigin(ctx.name.getTokenSource().getSourceName() + ":" + ctx.name.getLine());
        announceTaclet(ctx, r);
        schemaVariablesNamespace = schemaVariables().parent();
        return r;
    }

    private void announceTaclet(ParserRuleContext ctx, Taclet taclet) {
        RuleKey key = new RuleKey(taclet);
        TacletBuilder b = peek();
        if (b != null) {
            return;
        }
        taclets.add(taclet);
        /*if (parsedKeyFile.getTaclets().containsKey(key)) {
            //semanticError(ctx, "A taclet with name %s was already defined", key);
            System.err.format("Taclet clash with %s%n", key);
        }*/
        //System.out.format("ANNOUNCE: %s @ %s:%d%n", key, ctx.start.getTokenSource().getSourceName(), ctx.start.getLine());
        //parsedKeyFile.getTaclets().put(key, taclet);
    }

    @Override
    public Object visitModifiers(KeYParser.ModifiersContext ctx) {
        TacletBuilder b = peek();
        if (ctx.rs != null) {
            List<RuleSet> it = accept(ctx.rs);
            it.forEach(a -> b.addRuleSet(a));
        }

        if (ctx.NONINTERACTIVE() != null) {
            b.addRuleSet(ruleSets().lookup(new Name("notHumanReadable")));
        }

        if (ctx.DISPLAYNAME() != null) {
            b.setDisplayName(accept(ctx.dname));
        }

        if (ctx.HELPTEXT() != null) {
            b.setHelpText(accept(ctx.htext));
        }

        allOf(ctx.triggers());
        return null;
    }

    @Override
    public Sequent visitSeq(KeYParser.SeqContext ctx) {
        Semisequent ant = accept(ctx.ant);
        Semisequent suc = accept(ctx.suc);
        return Sequent.createSequent(ant, suc);
    }

    @Override
    public Object visitSeqEOF(KeYParser.SeqEOFContext ctx) {
        return accept(ctx.seq());
    }

    @Override
    public Object visitTermorseq(KeYParser.TermorseqContext ctx) {
        Term head = accept(ctx.head);
        Sequent s = accept(ctx.s);
        Semisequent ss = accept(ctx.ss);
        if (head != null && s == null && ss == null) {
            return head;
        }
        if (head != null && ss != null) {
            // A sequent with only head in the antecedent.
            Semisequent ant = Semisequent.EMPTY_SEMISEQUENT;
            ant = ant.insertFirst(
                    new SequentFormula(head)).semisequent();
            return Sequent.createSequent(ant, ss);
        }
        if (head != null && s != null) {
            // A sequent.  Prepend head to the antecedent.
            Semisequent newAnt = s.antecedent();
            newAnt = newAnt.insertFirst(
                    new SequentFormula(head)).semisequent();
            return Sequent.createSequent(newAnt, s.succedent());
        }
        if (ss != null) {
            return Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT, ss);
        }
        assert (false);
        return null;
    }

    @Override
    public Object visitSemisequent(KeYParser.SemisequentContext ctx) {
        Semisequent ss = accept(ctx.ss);
        if (ss == null)
            ss = Semisequent.EMPTY_SEMISEQUENT;
        Term head = accept(ctx.term());
        if (head != null)
            ss = ss.insertFirst(new SequentFormula(head)).semisequent();
        return ss;
    }

    @Override
    public Object visitVarexplist(KeYParser.VarexplistContext ctx) {
        return allOf(ctx.varexp());
    }

    @Override
    public Object visitVarexp(KeYParser.VarexpContext ctx) {
        negated = ctx.NOT_() != null;
        return super.visitVarexp(ctx);
        /*ctx.varcond_applyUpdateOnRigid()
                , ctx.varcond_dropEffectlessElementaries()
                , ctx.varcond_dropEffectlessStores()
                , ctx.varcond_enum_const()
                , ctx.varcond_free()
                , ctx.varcond_hassort()
                , ctx.varcond_fieldtype()
                , ctx.varcond_equalUnique()
                , ctx.varcond_new()
                , ctx.varcond_newlabel()
                , ctx.varcond_observer()
                , ctx.varcond_different()
                , ctx.varcond_metadisjoint()
                , ctx.varcond_simplifyIfThenElseUpdate()
                , ctx.varcond_differentFields()
                , ctx.varcond_sameObserver()
                , ctx.varcond_abstractOrInterface()
                , ctx.varcond_array()
                , ctx.varcond_array_length()
                , ctx.varcond_enumtype()
                , ctx.varcond_freeLabelIn()
                , ctx.varcond_localvariable()
                , ctx.varcond_thisreference()
                , ctx.varcond_reference()
                , ctx.varcond_referencearray()
                , ctx.varcond_static()
                , ctx.varcond_staticmethod()
                , ctx.varcond_mayexpandmethod()
                , ctx.varcond_final()
                , ctx.varcond_typecheck()
                , ctx.varcond_constant()
                , ctx.varcond_label()
                , ctx.varcond_static_field()
                , ctx.varcond_subFormulas()
                , ctx.varcond_containsAssignment());
    */
    }

    @Override
    public Object visitVarcond_sameObserver(KeYParser.Varcond_sameObserverContext ctx) {
        ParsableVariable t1 = accept(ctx.t1);
        ParsableVariable t2 = accept(ctx.t2);
        TacletBuilder b = peek();
        b.addVariableCondition(new SameObserverCondition(t1, t2));
        return null;
    }


    @Override
    public Object visitVarcond_applyUpdateOnRigid(KeYParser.Varcond_applyUpdateOnRigidContext ctx) {
        var u = accept(ctx.u);
        var x = accept(ctx.x);
        var x2 = accept(ctx.x2);
        TacletBuilder b = peek();
        b.addVariableCondition(new ApplyUpdateOnRigidCondition((UpdateSV) u,
                (SchemaVariable) x,
                (SchemaVariable) x2));
        return null;
    }

    @Override
    public Object visitVarcond_dropEffectlessElementaries(KeYParser.Varcond_dropEffectlessElementariesContext ctx) {
        UpdateSV u = accept(ctx.u);
        SchemaVariable x = accept(ctx.x);
        SchemaVariable result = accept(ctx.result);
        TacletBuilder b = peek();
        b.addVariableCondition(new DropEffectlessElementariesCondition(
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
        TacletBuilder b = peek();
        b.addVariableCondition(new DropEffectlessStoresCondition((TermSV) h,
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
        TacletBuilder b = peek();
        b.addVariableCondition(new DifferentFields((SchemaVariable) x, (SchemaVariable) y));
        return null;
    }

    @Override
    public Object visitVarcond_simplifyIfThenElseUpdate(KeYParser.Varcond_simplifyIfThenElseUpdateContext ctx) {
        FormulaSV phi = accept(ctx.phi);
        UpdateSV u1 = accept(ctx.u1);
        UpdateSV u2 = accept(ctx.u2);
        FormulaSV commonFormula = accept(ctx.commonFormula);
        SchemaVariable result = accept(ctx.result);
        TacletBuilder b = peek();
        b.addVariableCondition(new SimplifyIfThenElseUpdateCondition(phi,
                u1,
                u2,
                commonFormula,
                result));
        return null;
    }

    @Override
    public Object visitType_resolver(KeYParser.Type_resolverContext ctx) {
        Sort s = accept(ctx.any_sortId_check());
        var y = accept(ctx.y);
        if (s != null) {
            if (s instanceof GenericSort) {
                return TypeResolver.createGenericSortResolver((GenericSort) s);
            } else {
                return TypeResolver.createNonGenericSortResolver(s);
            }
        }
        if (ctx.TYPEOF() != null) {
            return TypeResolver.createElementTypeResolver((SchemaVariable) y);
        }
        if (ctx.CONTAINERTYPE() != null) {
            return TypeResolver.createContainerTypeResolver((SchemaVariable) y);
        }
        return null;
    }

    @Override
    public Object visitVarcond_new(KeYParser.Varcond_newContext ctx) {
        var x = accept(ctx.x);
        var y = accept(ctx.y);
        TacletBuilder b = peek();
        if (ctx.TYPEOF() != null) {
            b.addVarsNew((SchemaVariable) x, (SchemaVariable) y);
        }

        if (ctx.DEPENDINGON() != null) {
            b.addVarsNewDependingOn((SchemaVariable) x, (SchemaVariable) y);
        }

        if (ctx.kjt != null) {
            KeYJavaType kjt = accept(ctx.kjt);
            b.addVarsNew((SchemaVariable) x, kjt.getJavaType());
        }
        return null;
    }

    @Override
    public Object visitVarcond_newlabel(KeYParser.Varcond_newlabelContext ctx) {
        var x = accept(ctx.x);
        TacletBuilder b = peek();
        b.addVariableCondition(new NewJumpLabelCondition((SchemaVariable) x));
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
        TacletBuilder b = peek();
        b.addVariableCondition(new TypeComparisonCondition(fst, snd, mode));
        return null;
    }

    @Override
    public Object visitVarcond_free(KeYParser.Varcond_freeContext ctx) {
        SchemaVariable x = accept(ctx.x);
        List<SchemaVariable> ys = accept(ctx.varIds());
        TacletBuilder b = peek();
        ys.forEach(it -> b.addVarsNotFreeIn(x, it));
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
            TacletBuilder b = peek();
            b.addVariableCondition(new JavaTypeToSortCondition((SchemaVariable) x,
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
            TacletBuilder b = peek();
            b.addVariableCondition(new FieldTypeToSortCondition((SchemaVariable) x,
                    (GenericSort) s));
        }
        return null;
    }

    @Override
    public Object visitVarcond_containsAssignment(KeYParser.Varcond_containsAssignmentContext ctx) {
        var x = accept(ctx.x);
        TacletBuilder b = peek();
        b.addVariableCondition(new ContainsAssignmentCondition((SchemaVariable) x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_enumtype(KeYParser.Varcond_enumtypeContext ctx) {
        TypeResolver tr = accept(ctx.tr);
        TacletBuilder b = peek();
        b.addVariableCondition(new EnumTypeCondition(tr, negated));
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
        TacletBuilder b = peek();
        b.addVariableCondition(new TypeCondition(tr, !isPrimitive, nonNull));
        return null;
    }

    @Override
    public Object visitVarcond_thisreference(KeYParser.Varcond_thisreferenceContext ctx) {
        String id = null;
        boolean nonNull = false;
        ParsableVariable x = accept(ctx.x);
        TacletBuilder b = peek();
        b.addVariableCondition(new IsThisReference(x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_staticmethod(KeYParser.Varcond_staticmethodContext ctx) {
        var x = accept(ctx.x);
        var y = accept(ctx.y);
        var z = accept(ctx.z);
        TacletBuilder b = peek();
        b.addVariableCondition(new StaticMethodCondition
                (negated, (SchemaVariable) x, (SchemaVariable) y, (SchemaVariable) z));
        return null;
    }

    @Override
    public Object visitVarcond_mayexpandmethod(KeYParser.Varcond_mayexpandmethodContext ctx) {
        SchemaVariable x = accept(ctx.x);
        SchemaVariable y = accept(ctx.y);
        SchemaVariable z = accept(ctx.z);
        TacletBuilder b = peek();
        if (z != null)
            b.addVariableCondition(new MayExpandMethodCondition(
                    negated, x, y, z));
        else
            b.addVariableCondition(new MayExpandMethodCondition(
                    negated, null, x, y));
        return null;
    }

    @Override
    public Object visitVarcond_referencearray(KeYParser.Varcond_referencearrayContext ctx) {
        SchemaVariable x = accept(ctx.x);
        TacletBuilder b = peek();
        b.addVariableCondition(new ArrayComponentTypeCondition(
                x, !primitiveElementType));
        return null;
    }

    @Override
    public Object visitVarcond_array(KeYParser.Varcond_arrayContext ctx) {
        SchemaVariable x = accept(ctx.x);
        TacletBuilder b = peek();
        b.addVariableCondition(new ArrayTypeCondition(
                x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_array_length(KeYParser.Varcond_array_lengthContext ctx) {
        SchemaVariable x = accept(ctx.x);
        TacletBuilder b = peek();
        b.addVariableCondition(new ArrayLengthCondition(
                x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_abstractOrInterface(KeYParser.Varcond_abstractOrInterfaceContext ctx) {
        TypeResolver tr = accept(ctx.tr);
        TacletBuilder b = peek();
        b.addVariableCondition(new AbstractOrInterfaceType(tr, negated));
        return null;
    }

    @Override
    public Object visitVarcond_enum_const(KeYParser.Varcond_enum_constContext ctx) {
        SchemaVariable x = accept(ctx.x);
        TacletBuilder b = peek();
        b.addVariableCondition(new EnumConstantCondition(
                x));
        return null;
    }

    @Override
    public Object visitVarcond_final(KeYParser.Varcond_finalContext ctx) {
        SchemaVariable x = accept(ctx.x);
        TacletBuilder b = peek();
        b.addVariableCondition(new FinalReferenceCondition(
                x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_static(KeYParser.Varcond_staticContext ctx) {
        SchemaVariable x = accept(ctx.x);
        TacletBuilder b = peek();
        b.addVariableCondition(new StaticReferenceCondition(
                x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_localvariable(KeYParser.Varcond_localvariableContext ctx) {
        SchemaVariable x = accept(ctx.x);
        TacletBuilder b = peek();
        b.addVariableCondition(new LocalVariableCondition(x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_observer(KeYParser.Varcond_observerContext ctx) {
        TermSV obs = accept(ctx.obs);
        TermSV heap = accept(ctx.heap);

        TacletBuilder b = peek();
        b.addVariableCondition(new ObserverCondition(obs,
                heap));
        return null;
    }

    @Override
    public Object visitVarcond_different(KeYParser.Varcond_differentContext ctx) {
        SchemaVariable var1 = accept(ctx.var1);
        SchemaVariable var2 = accept(ctx.var2);
        TacletBuilder b = peek();
        b.addVariableCondition(new DifferentInstantiationCondition(
                var1,
                var2));
        return null;
    }

    @Override
    public Object visitVarcond_metadisjoint(KeYParser.Varcond_metadisjointContext ctx) {
        var var1 = accept(ctx.var1);
        var var2 = accept(ctx.var2);
        TacletBuilder b = peek();
        b.addVariableCondition(new MetaDisjointCondition(
                (TermSV) var1,
                (TermSV) var2));
        return null;
    }

    @Override
    public Object visitVarcond_equalUnique(KeYParser.Varcond_equalUniqueContext ctx) {
        var t = accept(ctx.t);
        var t2 = accept(ctx.t2);
        var phi = accept(ctx.phi);
        TacletBuilder b = peek();
        b.addVariableCondition(new EqualUniqueCondition((TermSV) t,
                (TermSV) t2,
                (FormulaSV) phi));
        return null;
    }

    @Override
    public Object visitVarcond_freeLabelIn(KeYParser.Varcond_freeLabelInContext ctx) {
        var l = accept(ctx.l);
        var statement = accept(ctx.statement);
        TacletBuilder b = peek();
        b.addVariableCondition(new FreeLabelInVariableCondition((SchemaVariable) l,
                (SchemaVariable) statement, negated));
        return null;
    }

    @Override
    public Object visitVarcond_constant(KeYParser.Varcond_constantContext ctx) {
        var x = accept(ctx.varId());
        TacletBuilder b = peek();
        if (x instanceof TermSV) {
            b.addVariableCondition(new ConstantCondition((TermSV) x, negated));
        } else {
            assert x instanceof FormulaSV;
            b.addVariableCondition(new ConstantCondition((FormulaSV) x, negated));
        }
        return null;
    }

    @Override
    public Object visitVarcond_label(KeYParser.Varcond_labelContext ctx) {
        TermLabelSV l = accept(ctx.varId());
        String name = accept(ctx.simple_ident());
        TacletBuilder b = peek();
        b.addVariableCondition(new TermLabelCondition(l, name, negated));
        return null;
    }

    @Override
    public Object visitVarcond_static_field(KeYParser.Varcond_static_fieldContext ctx) {
        var field = accept(ctx.varId());
        TacletBuilder b = peek();
        b.addVariableCondition(new StaticFieldCondition((SchemaVariable) field, negated));
        return null;
    }

    @Override
    public Object visitVarcond_subFormulas(KeYParser.Varcond_subFormulasContext ctx) {
        FormulaSV x = accept(ctx.varId());
        TacletBuilder b = peek();
        b.addVariableCondition(new SubFormulaCondition(x, negated));
        return null;
    }

    @Override
    public Object visitGoalspecs(KeYParser.GoalspecsContext ctx) {
        return allOf(ctx.goalspecwithoption());
    }

    @Override
    public Object visitGoalspecwithoption(KeYParser.GoalspecwithoptionContext ctx) {
        //TODO
        var soc = accept(ctx.option_list());
        accept(ctx.goalspec());
        return null;
    }

    @Override
    public Object visitOption(KeYParser.OptionContext ctx) {
        String choice = ctx.getText();
        var c = choices().lookup(choice);
        if (c == null) {
            semanticError(ctx, "Could not find choice: %s", choice);
        }
        return c;
    }

    @Override
    public List<Choice> visitOption_list(KeYParser.Option_listContext ctx) {
        return allOf(ctx.option());
    }

    @Override
    public Object visitGoalspec(KeYParser.GoalspecContext ctx) {
        ImmutableSet<Choice> soc = ImmutableSet.empty();
        boolean ruleWithFind;
        var addSeq = Sequent.EMPTY_SEQUENT;
        var addRList = ImmutableSLList.<Taclet>nil();
        var addpv = DefaultImmutableSet.<SchemaVariable>nil();

        String name = accept(ctx.string_value());

        var rwObj = accept(ctx.replacewith());
        if (ctx.add() != null) addSeq = accept(ctx.add());
        if (ctx.addrules() != null) addRList = accept(ctx.addrules());
        if (ctx.addprogvar() != null) addpv = accept(ctx.addprogvar());
        TacletBuilder b = peek();
        addGoalTemplate(b, name, rwObj, addSeq, addRList, addpv, soc, ctx);
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
        List<Taclet> taclets = allOf(ctx.taclet());
        return ImmutableList.fromList(taclets);
    }


    /*private boolean isTermTransformer()  {
        return (input.LA(1) == KeYLexer.IDENT &&
                AbstractTermTransformer.name2metaop(input.LT(1).getText()) != null)
                || input.LA(1) == KeYLexer.IN_TYPE;
    }

    private boolean isStaticQuery() {
        if (inSchemaMode()) return false;
        final JavaInfo javaInfo = getJavaInfo();
        boolean result = false;
//    try {
        int n = 1;
        KeYJavaType kjt = null;
        StringBuffer className = new StringBuffer(input.LT(n).getText());
        while (isPackage(className.toString())) {
            if (input.LA(n + 1) != KeYLexer.DOT) return false;
            className.append(".");
            className.append(input.LT(n + 2).getText());
            n += 2;
        }
        kjt = getTypeByClassName(className.toString());
        if (kjt != null) {
            if (input.LA(n + 1) == KeYLexer.DOT && input.LA(n + 3) == KeYLexer.LPAREN) {
                Iterator<IProgramMethod> it = javaInfo.getAllProgramMethods(kjt).iterator();
                while (it.hasNext()) {
                    final IProgramMethod pm = it.next();
                    final String name = kjt.getFullName() + "::" + input.LT(n + 2).getText();
                    if (pm != null && pm.isStatic() && pm.name().toString().equals(name)) {
                        result = true;
                        break;
                    }
                }
            }
        }
        return result;
    }
*/
    private TacletBuilder createTacletBuilderFor(Object find, int applicationRestriction, ParserRuleContext ctx) {
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

    private void addGoalTemplate(TacletBuilder b,
                                 String id,
                                 Object rwObj,
                                 Sequent addSeq,
                                 ImmutableList<Taclet> addRList,
                                 ImmutableSet<SchemaVariable> pvs,
                                 ImmutableSet<Choice> soc, ParserRuleContext ctx) {
        TacletGoalTemplate gt = null;
        if (rwObj == null) {
            // there is no replacewith, so we take
            gt = new TacletGoalTemplate(addSeq,
                    addRList,
                    pvs);
        } else {
            if (b instanceof NoFindTacletBuilder) {
                // there is a replacewith without a find.
                throwEx(new RecognitionException(""));
                //new UnfittingReplacewithException
                //("Replacewith without find", getSourceName(),
                // getLine(), getColumn());
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
        assert gt != null;
        gt.setName(id);
        b.addTacletGoalTemplate(gt);
        if (soc != null) b.addGoal2ChoicesMapping(gt, soc);
    }

    @Override
    public Object visitVarId(KeYParser.VarIdContext ctx) {
        var id = ctx.id.getText();
        var v = variables().lookup(new Name(ctx.id.getText()));
        if (v == null) {
            v = (QuantifiableVariable) schemaVariables().lookup(new Name(id));
        }
        if (v == null) {
            semanticError(ctx, "variable %s", id);
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

        if (ctx.any_sortId_check() != null)
            s = accept(ctx.any_sortId_check());

        try {
            for (String id : ids) {
                schema_var_decl(id,
                        s,
                        makeVariableSV,
                        makeSkolemTermSV,
                        makeTermLabelSV,
                        mods);
            }
        } catch (AmbigiousDeclException e) {
            throwEx(e);
        }
        return null;
    }

    @Override
    public Object visitSchema_modifiers(KeYParser.Schema_modifiersContext ctx) {
        SchemaVariableModifierSet mods = pop();
        var ids = visitSimple_ident_comma_list(ctx.simple_ident_comma_list());
        for (String id : ids) {
            if (!mods.addModifier(id))
                semanticError(ctx, "Illegal or unknown modifier in declaration of schema variable: %s", id);
        }
        return null;
    }

    @Override
    public Object visitSchema_var_decls(KeYParser.Schema_var_declsContext ctx) {
        List<SchemaVariable> seq = allOf(ctx.one_schema_var_decl());
        return seq;
    }

    public List<Taclet> getTaclets() {
        return taclets;
    }
}
