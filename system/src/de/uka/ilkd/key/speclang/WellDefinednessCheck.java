package de.uka.ilkd.key.speclang;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.label.ImplicitSpecTermLabel;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.WellDefinednessPO;
import de.uka.ilkd.key.proof.init.WellDefinednessPO.Variables;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.speclang.jml.JMLInfoExtractor;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

/**
 * A contract for checking the well-definedness of a specification element
 * (i.e. a class invariant, a method contract, a loop invariant or a block contract),
 * consisting of precondition, assignable-clause and postcondition/invariant
 * (depending on which kind of contract it is).
 */
/**
 * @author kirsten
 *
 */
public abstract class WellDefinednessCheck implements Contract {

    protected static final TermBuilder TB = TermBuilder.DF;
    protected static final TermFactory TF = TermFactory.DEFAULT;

    public static final String INV_TACLET = "wd_Invariant_";
    public static final String OP_TACLET = "wd_Operation_";
    private static final ITermLabel IMPLICIT = ImplicitSpecTermLabel.INSTANCE;

    static enum Type {
        CLASS_INVARIANT, CLASS_AXIOM, OPERATION_CONTRACT, LOOP_INVARIANT, BLOCK_CONTRACT;
    }

    private final String name;
    private final int id;
    private final Type type;
    private IObserverFunction target;
    private final LocationVariable heap;
    private final OriginalVariables origVars;

    private Condition requires;
    private Term assignable;
    private Condition ensures;
    private Term accessible;
    private Term mby;
    private Term represents;

    WellDefinednessCheck(String name, int id, IObserverFunction target,
                         OriginalVariables origVars, Type type, Services services) {
        this.id = id;
        this.name = name +" WD." + id;
        this.type = type;
        this.target = target;
        this.heap = services.getTypeConverter().getHeapLDT().getHeap();
        this.origVars = origVars;
    }

    WellDefinednessCheck(String name, int id, Type type, IObserverFunction target,
                         LocationVariable heap, OriginalVariables origVars,
                         Condition requires, Term assignable, Term accessible,
                         Condition ensures, Term mby, Term represents) {
        this.name = name;
        this.id = id;
        this.type = type;
        this.target = target;
        this.heap = heap;
        this.origVars = origVars;
        this.requires = requires;
        this.assignable = assignable;
        this.accessible = accessible;
        this.ensures = ensures;
        this.mby = mby;
        this.represents = represents;
    }

    //-------------------------------------------------------------------------
    // Internal Methods
    //-------------------------------------------------------------------------

    private static Term removeImplicitSpecLabel(Term t) {
        ImmutableArray<ITermLabel> ls = t.getLabels();
        LinkedList<ITermLabel> res = new LinkedList<ITermLabel>();
        for (ITermLabel l: ls) {
            if(!l.equals(IMPLICIT)) {
                res.add(l);
            }
        }
        if (res.isEmpty()) {
            ls = new ImmutableArray<ITermLabel>();
        } else {
            ls = new ImmutableArray<ITermLabel>(res);
        }
        res.clear();
        if (t.arity() > 1) {
            Term[] subs = new Term[t.arity()];
            int i = 0;
            for(Term sub: t.subs()) {
                subs[i++] = removeImplicitSpecLabel(sub);
            }
            t = TF.createTerm(t.op(), subs, t.getLabels());
        }
        return TB.relabel(t, ls);
    }

    private static Pair<Term, Term> split(Term spec) {
        Pair<ImmutableList<Term>, ImmutableList<Term>> p = splitAndRelabel(spec);
        ImmutableList<Term> start = p.first;
        ImmutableList<Term> end   = p.second;
        return new Pair<Term, Term> (TB.andSC(start), TB.andSC(end));
    }

    private static Pair<ImmutableList<Term>, ImmutableList<Term>> splitAndRelabel(Term spec) {
        assert spec != null;
        ImmutableList<Term> start = ImmutableSLList.<Term>nil();
        ImmutableList<Term> end = ImmutableSLList.<Term>nil();
        if(spec.arity() > 0
                && spec.op().equals(Junctor.AND)) {
            for (Term sub: spec.subs()) {
                if(sub.hasLabels()
                        && sub.getLabels().contains(IMPLICIT)) {
                    sub = removeImplicitSpecLabel(sub);
                    Pair<ImmutableList<Term>, ImmutableList<Term>> p = splitAndRelabel(sub);
                    start = start.append(p.first).append(p.second);
                } else {
                    Pair<ImmutableList<Term>, ImmutableList<Term>> p = splitAndRelabel(sub);
                    start = start.append(p.first);
                    end = end.append(p.second);
                }
            }
            return new Pair<ImmutableList<Term>, ImmutableList<Term>> (start, end);
        } else if (spec.arity() > 0
                && spec.op().equals(Junctor.IMP)) {
            assert spec.arity() == 2;
            Pair<ImmutableList<Term>, ImmutableList<Term>> imp1 = splitAndRelabel(spec.sub(0));
            Pair<ImmutableList<Term>, ImmutableList<Term>> imp2 = splitAndRelabel(spec.sub(1));
            Term i1 = TB.andSC(TB.andSC(imp1.first), TB.andSC(imp1.second));
            Term i2 = TB.andSC(TB.andSC(imp2.first), TB.andSC(imp2.second));
            end = end.append(TB.imp(i1, i2));
            return new Pair<ImmutableList<Term>, ImmutableList<Term>> (start, end);
        } else {
            if(spec.hasLabels()
                    && spec.getLabels().contains(IMPLICIT)) {
                spec = removeImplicitSpecLabel(spec);
            }
            end = end.append(spec);
            return new Pair<ImmutableList<Term>, ImmutableList<Term>> (start, end);
        }
    }

    private static Term replaceSV(Term t, SchemaVariable self,
                                  ImmutableList<ParsableVariable> params,
                                  WellDefinednessCheck check) {
        return replaceSV(t, self, null, null, null, params,
                         check.getOrigVars(), check.getHeaps());
    }

    private static Term replace(Term t, Variables vars,
                                WellDefinednessCheck check) {
        return replace(t, vars.self, vars.result, vars.exception, vars.atPres,
                       vars.params, check.getOrigVars(), check.getHeaps());
    }

    private static Term replaceSV(Term t,
                                  SchemaVariable selfVar,
                                  SchemaVariable resultVar,
                                  SchemaVariable excVar,
                                  Map<LocationVariable,
                                      SchemaVariable> atPreVars,
                                  ImmutableList<ParsableVariable> paramVars,
                                  OriginalVariables origVars,
                                  ImmutableList<LocationVariable> heaps) {
        Map<ProgramVariable, SchemaVariable> map =
                getSchemaMap(selfVar, resultVar, excVar, atPreVars,
                             paramVars, origVars, heaps);
        final OpReplacer or = new OpReplacer(map);
        return or.replace(t);
    }

    private static Term replace(Term t,
                                ProgramVariable selfVar,
                                ProgramVariable resultVar,
                                ProgramVariable excVar,
                                Map<LocationVariable,
                                    ProgramVariable> atPreVars,
                                ImmutableList<ProgramVariable> paramVars,
                                OriginalVariables origVars,
                                ImmutableList<LocationVariable> heaps) {
        Map<ProgramVariable, ProgramVariable> map =
                getReplaceMap(selfVar, resultVar, excVar, atPreVars,
                              paramVars, origVars, heaps);
        final OpReplacer or = new OpReplacer(map);
        return or.replace(t);
    }

    private static Map<ProgramVariable, SchemaVariable>
                                getSchemaMap(SchemaVariable selfVar,
                                             SchemaVariable resultVar,
                                             SchemaVariable excVar,
                                             Map<LocationVariable,
                                                 SchemaVariable> atPreVars,
                                             ImmutableList<ParsableVariable> paramVars,
                                             OriginalVariables vars,
                                             ImmutableList<LocationVariable> heaps) {
        final Map<ProgramVariable, SchemaVariable> result =
                new LinkedHashMap<ProgramVariable, SchemaVariable>();
        //self
        if(selfVar != null && vars.self != null) {
            assert selfVar.sort().extendsTrans(vars.self.sort());
            result.put(vars.self, selfVar);
        }
        //parameters
        if(paramVars != null && vars.params != null
                && !paramVars.isEmpty() && !vars.params.isEmpty()) {
            assert vars.params.size() == paramVars.size();
            final Iterator<ProgramVariable> it1 = vars.params.iterator();
            final Iterator<ParsableVariable> it2 = paramVars.iterator();
            while(it1.hasNext()) {
                ProgramVariable originalParamVar = it1.next();
                ParsableVariable paramVar          = it2.next();
                assert paramVar instanceof SchemaVariable;
                SchemaVariable paramSV = (SchemaVariable)paramVar;
                assert originalParamVar.sort().equals(paramSV.sort());
                result.put(originalParamVar, paramSV);
            }
        }
        //result
        if(resultVar != null && vars.result != null) {
            assert vars.result.sort().equals(resultVar.sort());
            result.put(vars.result, resultVar);
        }
        //exception
        if(excVar != null && vars.exception != null) {
            assert vars.exception.sort().equals(excVar.sort());
            result.put(vars.exception, excVar);
        }
        if(atPreVars != null && vars.atPres != null
                && !atPreVars.isEmpty() && !vars.atPres.isEmpty()) {
            for(LocationVariable h : heaps) {
                if(atPreVars.get(h) != null && vars.atPres.get(h) != null) {
                    assert vars.atPres.get(h).sort().equals(atPreVars.get(h).sort());
                    result.put(vars.atPres.get(h), atPreVars.get(h));
                }
            }
        }
        return result;
    }

    private static Map<ProgramVariable, ProgramVariable>
                                getReplaceMap(ProgramVariable selfVar,
                                              ProgramVariable resultVar,
                                              ProgramVariable excVar,
                                              Map<LocationVariable,
                                                  ProgramVariable> atPreVars,
                                              ImmutableList<ProgramVariable> paramVars,
                                              OriginalVariables vars,
                                              ImmutableList<LocationVariable> heaps) {
        final Map<ProgramVariable, ProgramVariable> result =
                new LinkedHashMap<ProgramVariable, ProgramVariable>();
        //self
        if(selfVar != null && vars.self != null) {
            assert selfVar.sort().extendsTrans(vars.self.sort());
            result.put(vars.self, selfVar);
        }
        //parameters
        if(paramVars != null && vars.params != null
                && !paramVars.isEmpty() && !vars.params.isEmpty()) {
            assert vars.params.size() == paramVars.size();
            final Iterator<ProgramVariable> it1 = vars.params.iterator();
            final Iterator<ProgramVariable> it2 = paramVars.iterator();
            while(it1.hasNext()) {
                ProgramVariable originalParamVar = it1.next();
                ProgramVariable paramVar         = it2.next();
                assert originalParamVar.sort().equals(paramVar.sort());
                result.put(originalParamVar, paramVar);
            }
        }
        //result
        if(resultVar != null && vars.result != null) {
            assert vars.result.sort().equals(resultVar.sort());
            result.put(vars.result, resultVar);
        }
        //exception
        if(excVar != null && vars.exception != null) {
            assert vars.exception.sort().equals(excVar.sort());
            result.put(vars.exception, excVar);
        }
        if(atPreVars != null && vars.atPres != null
                && !atPreVars.isEmpty() && !vars.atPres.isEmpty()) {
            for(LocationVariable h : heaps) {
                if(atPreVars.get(h) != null && vars.atPres.get(h) != null) {
                    assert vars.atPres.get(h).sort().equals(atPreVars.get(h).sort());
                    result.put(vars.atPres.get(h), atPreVars.get(h));
                }
            }
        }
        return result;
    }

    private Term replace(Term t, Variables vars) {
        return replace(t, vars, this);
    }

    private Condition replace(Condition pre, Variables vars) {
        final Term implicit = replace(pre.implicit, vars);
        final Term explicit = replace(pre.explicit, vars);
        return new Condition(implicit, explicit);
    }

    private ImmutableList<Term> replace(Iterable<Term> l, Variables vars) {
        ImmutableList<Term> res = ImmutableSLList.<Term>nil();
        for (Term t: l) {
            res = res.append(replace(t, vars));
        }
        return res;
    }

    private Term replaceSV(Term t, SchemaVariable self,
                           ImmutableList<ParsableVariable> params) {
        return replaceSV(t, self, params, this);
    }

    private ImmutableList<LocationVariable> getHeaps() {
        ImmutableList<LocationVariable> result =
                ImmutableSLList.<LocationVariable>nil();
        return result.append(getHeap());
    }

    private String typeString() {
        return type().toString().toLowerCase().replace("_", " ");
    }

    private String getText(boolean includeHtmlMarkup, Services services) {
        final StringBuffer sig = new StringBuffer();
        OriginalVariables origVars = getOrigVars();
        if (origVars.result != null) {
            sig.append(origVars.result);
            sig.append(" = ");
        }
        else if (isConstructor()) {
            sig.append(origVars.self);
            sig.append(" = new ");
        }
        if (!target.isStatic() && !isConstructor()) {
            sig.append(origVars.self);
            sig.append(".");
        }
        sig.append(target instanceof IProgramMethod ?
                ((IProgramMethod)target).getName() : "");
        sig.append("(");
        for (ProgramVariable pv : origVars.params) {
            sig.append(pv.name()).append(", ");
        }
        if (!origVars.params.isEmpty()) {
            sig.setLength(sig.length() - 2);
        }
        sig.append(")");
        if(!isModel()) {
            sig.append(" catch(");
            sig.append(origVars.exception);
            sig.append(")");
        }
        String mods = "";
        if (getAssignable(null) != null) {
            String printMods = LogicPrinter.quickPrintTerm(getAssignable(null), services);
            mods = mods
                    + (includeHtmlMarkup ? "<br><b>" : "\n")
                    + "mod"
                    + (includeHtmlMarkup ? "</b> " : ": ")
                    + (includeHtmlMarkup ?
                            LogicPrinter.escapeHTML(printMods, false) : printMods.trim());
        }
        String pres = "";
        if (getRequires(null) != null) {
            String printPres = LogicPrinter.quickPrintTerm(getRequires(null), services);
            pres = pres
                    + (includeHtmlMarkup ? "<br><b>" : "\n")
                    + "pre"
                    + (includeHtmlMarkup ? "</b> " : ": ")
                    + (includeHtmlMarkup ?
                            LogicPrinter.escapeHTML(printPres, false) : printPres.trim());
        }
        String posts = "";
        for (LocationVariable h : getHeaps()) {
            if (getEnsures() != null) {
                String printPosts = LogicPrinter.quickPrintTerm(getEnsures(null), services);
                posts = posts
                        + (includeHtmlMarkup ? "<br><b>" : "\n")
                        + "post"
                        + (h == getHeap() ? "" : "[" + h + "]")
                        + (includeHtmlMarkup ? "</b> " : ": ")
                        + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printPosts, false)
                                : printPosts.trim());
            }
        }
        if (includeHtmlMarkup) {
            return "<html>"
                    + "<i>"
                    + LogicPrinter.escapeHTML(sig.toString(), false)
                    + "</i>"
                    + pres
                    + posts
                    + mods
                    + (transactionApplicableContract() ? "<br><b>transaction applicable</b>" : "") +
                    "</html>";
        } else {
            return sig.toString()
                    + pres
                    + posts
                    + mods
                    + (transactionApplicableContract() ? "\ntransaction applicable:" : "");
        }
    }

    private Term appendFreePre(Term pre,
                               ParsableVariable self,
                               ParsableVariable heap,
                               Services services) {
        final IObserverFunction target = getTarget();
        final KeYJavaType selfKJT = target.getContainerType();
        final Term notNull = target.isStatic() ?
                TB.tt() : TB.not(TB.equals(TB.var(self), TB.NULL(services)));
        final Term created = TB.created(services, TB.var(heap), TB.var(self));
        final Term selfExactType =
                TB.exactInstance(services, selfKJT.getSort(), TB.var(self));
        return TB.andSC(pre, notNull, created, selfExactType);
    }

    /**
     * Generates the general assumption that self is not null.
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @return The term representing the general assumption.
     */
    private Term generateSelfNotNull(ParsableVariable selfVar, Services services) {
        return selfVar == null || isConstructor() ?
                TB.tt() : TB.not(TB.equals(TB.var(selfVar), TB.NULL(services)));
    }

    /**
     * Generates the general assumption that self is created.
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @return The term representing the general assumption.
     */
    private Term generateSelfCreated(ParsableVariable selfVar, ParsableVariable heap,
                                     Services services) {
        if(selfVar == null || isConstructor()) {
            return TB.tt();
        } else {
            return TB.created(services, TB.var(heap), TB.var(selfVar));
        }
    }


    /**
     * Generates the general assumption which defines the type of self.
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @param selfKJT The {@link KeYJavaType} of the self variable.
     * @return The term representing the general assumption.
     */
    private Term generateSelfExactType(ParsableVariable selfVar, Services services) {
        return selfVar == null || isConstructor() ? TB.tt() :
            TB.exactInstance(services, getKJT().getSort(),
                             TB.var(selfVar));
    }

    /**
     * Generates the general assumption that all parameter arguments are valid.
     * @param paramVars The parameters {@link ProgramVariable}s.
     * @return The term representing the general assumption.
     */
    private Term generateParamsOK(ImmutableList<ParsableVariable> paramVars, Services services) {
        Term paramsOK = TB.tt();
        if (paramVars.size() == getOrigVars().params.size()) {
            final Iterator<ProgramVariable> origParams = getOrigVars().params.iterator();
            for (ParsableVariable paramVar : paramVars) {
                assert origParams.hasNext();
                paramsOK = TB.and(paramsOK,
                                  TB.reachableValue(services, TB.var(paramVar),
                                                    origParams.next().getKeYJavaType()));
            }
        } else {
            for (ParsableVariable paramVar : paramVars) {
                assert paramVar instanceof ProgramVariable;
                ProgramVariable pv = (ProgramVariable)paramVar;
                paramsOK = TB.and(paramsOK,
                                  TB.reachableValue(services, TB.var(paramVar),
                                                    pv.getKeYJavaType()));
            }
        }
        return paramsOK;
    }

    /**
     * Builds the "general assumption" using the self variable (self),
     * the {@link KeYJavaType} of the self variable (selfKJT),
     * the parameters {@link ProgramVariable}s (paramVars), the heaps (heaps), and
     * @param the implicit precondition
     * @return The {@link Term} containing the general assumptions.
     */
    private TermListAndFunc buildFreePre(Term implicitPre, ParsableVariable self,
                                         ParsableVariable heap,
                                         ImmutableList<ParsableVariable> params,
                                         boolean taclet,
                                         Services services) {
        ImmutableList<Term> resList = ImmutableSLList.<Term>nil();

        // "self != null"
        final Term selfNotNull = generateSelfNotNull(self, services);

        // "self.<created> = TRUE"
        final Term selfCreated = generateSelfCreated(self, heap, services);

        // "MyClass::exactInstance(self) = TRUE"
        final Term selfExactType = generateSelfExactType(self, services);

        // conjunction of...
        // - "p_i = null | p_i.<created> = TRUE" for object parameters, and
        // - "inBounds(p_i)" for integer parameters
        Term paramsOK = generateParamsOK(params, services);

        // initial value of measured_by clause
        final TermAndFunc mbyAtPreDef = generateMbyAtPreDef(self, params, services);
        final Term wellFormed = TB.wellFormed(TB.var(heap), services);
        final Term[] result;
        if (!taclet) {
            result = new Term[]
                    { wellFormed, selfNotNull, selfCreated, selfExactType,
                    implicitPre, paramsOK, mbyAtPreDef.term };
        } else {
            result = new Term[]
                    { wellFormed, implicitPre, paramsOK, mbyAtPreDef.term };
        }
        for (Term t: result) {
            resList = resList.append(t);
        }
        return new TermListAndFunc(resList, mbyAtPreDef.func);
    }

    abstract TermAndFunc generateMbyAtPreDef(ParsableVariable self,
                                             ImmutableList<ParsableVariable> params,
                                             Services services);

    final Condition replaceSV(Condition pre, SchemaVariable self,
                              ImmutableList<ParsableVariable> params) {
        final Term implicit = replaceSV(pre.implicit, self, params);
        final Term explicit = replaceSV(pre.explicit, self, params);
        return new Condition(implicit, explicit);
    }

    final void setMby(Term mby) {
        this.mby = mby;
    }

    final void setRequires(Term req) {
        Pair<Term, Term> requires = split(req);
        this.requires = new Condition(requires.first, requires.second);
    }

    final void setAssignable(Term ass, Services services) {
        this.assignable = ass;
        if (ass == TB.ff()) {
            this.assignable = TB.empty(services);
        } else if (ass == TB.tt()) {
            this.assignable = TB.allLocs(services);
        }
    }

    final void setAccessible(Term acc) {
        this.accessible = acc;
    }

    final void addEnsures(Term ens) {
        final Pair<Term, Term> ensures = split(ens);
        final Condition oldEnsures = getEnsures();
        this.ensures = new Condition(TB.andSC(ensures.first, oldEnsures.implicit),
                                     TB.andSC(ensures.second, oldEnsures.explicit));
    }

    final void setEnsures(Term ens) {
        Pair<Term, Term> ensures = split(ens);
        this.ensures = new Condition(ensures.first, ensures.second);
    }

    final Type type() {
        return this.type;
    }

    ImmutableList<Term> getRest() {
        ImmutableList<Term> rest = ImmutableSLList.<Term>nil();
        final Term accessible = this.accessible;
        if (accessible != null) {
            rest = rest.append(accessible);
        }
        final Term mby = this.mby;
        if (mby != null) {
            rest = rest.append(mby);
        }
        final Term represents = this.represents;
        if (represents != null) {
            rest = rest.append(represents);
        }
        return rest;
    }

    //-------------------------------------------------------------------------
    // Public Interface
    //-------------------------------------------------------------------------

    public abstract String getBehaviour();

    public abstract boolean isModel();

    public final static Taclet createTaclet(String name,
                                            Term callee,
                                            Term callTerm,
                                            Term pre,
                                            boolean isStatic,
                                            Services services) {
        final RewriteTacletBuilder tb = new RewriteTacletBuilder();
        final Term notNull = isStatic ?
                TB.tt() : TB.not(TB.equals(callee, TB.NULL(services)));
        final Term created = isStatic ?
                TB.tt() : TB.created(services, callee);
        tb.setFind(TB.wd(callTerm, services));
        tb.setName(MiscTools.toValidTacletName(name));
        tb.addRuleSet(new RuleSet(new Name("simplify")));
        tb.addGoalTerm(TB.andSC(notNull, created, pre));
        return tb.getTaclet();
    }

    /** collects terms for precondition,
     * assignable clause and other specification elements,
     * and postcondition & signals-clause */
    public final POTerms createPOTerms() {
        final Condition pre = this.getRequires();
        final Term mod = this.getAssignable();
        final ImmutableList<Term> rest = this.getRest();
        final Condition post = this.getEnsures();
        return new POTerms(pre, mod, rest, post);
    }

    public final WellDefinednessCheck addRepresents(Term rep) {
        this.represents = rep;
        return this;
    }

    public final TermAndFunc getPre(final Condition pre,
                                    ParsableVariable self,
                                    ParsableVariable heap,
                                    ImmutableList<? extends ParsableVariable> parameters,
                                    boolean taclet,
                                    Services services) {
        ImmutableList<ParsableVariable> params = ImmutableSLList.<ParsableVariable>nil();
        for (ParsableVariable pv: parameters) {
            params = params.append(pv);
        }
        final IObserverFunction target = getTarget();
        final TermListAndFunc freePre =
                buildFreePre(pre.implicit, self, heap, params, taclet, services);
        final ImmutableList<Term> preTerms = freePre.terms.append(pre.explicit);
        Term res = TB.andSC(preTerms);
        if (!taclet
                && target instanceof IProgramMethod
                && ((IProgramMethod)target).isConstructor()
                && !JMLInfoExtractor.isHelper((IProgramMethod)target)) {
            final Term constructorPre =
                    appendFreePre(res, self, heap, services);
            return new TermAndFunc(constructorPre, freePre.func);
        } else {
            return new TermAndFunc(res, freePre.func);
        }
    }

    public final Term getPost(final Condition post, ParsableVariable result,
                              Services services) {
        final Term reachable;
        if (result != null) {
            reachable = TB.reachableValue(services, TB.var(result),
                                          origVars.result.getKeYJavaType());
        } else {
            reachable = TB.tt();
        }
        return TB.andSC(reachable, post.implicit, post.explicit);
    }

    public final Term getUpdates(Term mod, LocationVariable heap,
                                 ProgramVariable heapAtPre,
                                 Term anonHeap, Services services) {
        assert mod != null;
        final Term havocUpd = TB.elementary(services, heap,
                TB.anon(services, TB.var(heap), mod, anonHeap));
        final Term oldUpd = TB.elementary(services, TB.var(heapAtPre), TB.var(heap));
        return TB.parallel(oldUpd, havocUpd);
    }

    public final POTerms replace(POTerms po, Variables vars) {
        final Condition pre = replace(po.pre, vars);
        final Term mod = replace(po.mod, vars);
        final ImmutableList<Term> rest = replace(po.rest, vars);
        final Condition post = replace(po.post, vars);
        return new POTerms(pre, mod, rest, post);
    }

    public final LocationVariable getHeap() {
        return this.heap;
    }

    public final Name name() {
        return new Name(getName());
    }

    public final Condition getRequires() {
        assert this.requires != null;
        return this.requires;
    }

    public final Term getAssignable() {
        assert this.assignable != null;
        return this.assignable;
    }

    public final Term getAccessible() {
        return this.accessible;
    }

    public final Condition getEnsures() {
        assert this.ensures != null;
        return this.ensures;
    }

    public final Term getEnsures(LocationVariable heap) {
        return TB.andSC(getEnsures().implicit, getEnsures().explicit);
    }

    public final Term getRepresents() {
        return this.represents;
    }

    public final boolean isConstructor() {
        IObserverFunction target = getTarget();
        return target instanceof IProgramMethod
                && ((IProgramMethod)target).isConstructor();
    }

    @Override
    public final String toString() {
        return getName();
    }

    @Override
    public final String getName() {
        return this.name;
    }

    @Override
    public final int id() {
        return id;
    }

    @Override
    public final Term getMby() {
        return this.mby;
    }

    @Override
    public final boolean hasMby() {
        return this.mby != null;
    }

    @Override
    public final Term getRequires(LocationVariable heap) {
        return TB.andSC(getRequires().implicit, getRequires().explicit);
    }

    public final Term getAssignable(LocationVariable heap) {
        return getAssignable();
    }

    public final Term getAccessible(ProgramVariable heap) {
        return getAccessible();
    }

    @Override
    public final String getHTMLText(Services services) {
        return getText(true, services);
    }

    @Override
    public final String getPlainText(Services services) {
        return getText(false, services);
    }

    @Override
    public final String proofToString(Services services) {
        assert false;
        return null;
    }

    @Override
    public final IObserverFunction getTarget() {
        return this.target;
    }

    @Override
    public final ProofOblInput createProofObl(InitConfig initConfig, Contract contract) {
        assert contract instanceof WellDefinednessCheck;
        return new WellDefinednessPO(initConfig, (WellDefinednessCheck) contract);
    }

    @Override
    public final String getDisplayName() {
        return "Well-Definedness of JML " +
               (isModel() ? "model " : "") +
               typeString() +
               (type() != Type.CLASS_INVARIANT ? (" " + id) : "") +
               getBehaviour();
    }

    @Override
    public final boolean toBeSaved() {
        return false;
    }

    public final boolean hasSelfVar() {
        return origVars.self != null;
    }

    @Override
    public final OriginalVariables getOrigVars() {
        return this.origVars;
    }

    @Override
    public final boolean equals(Object o) {
        if (!(o instanceof WellDefinednessCheck)) {
            return false;
        }
        WellDefinednessCheck wd = (WellDefinednessCheck)o;
        return wd.getName().equals(this.name);
    }

    @Override
    public final int hashCode() {
        return this.name.hashCode();
    }

    @Deprecated
    public final Term getPre(LocationVariable heap, ProgramVariable selfVar,
                             ImmutableList<ProgramVariable> paramVars,
                             Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                             Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public final Term getPre(List<LocationVariable> heapContext,
                             ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
                             Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                             Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public final Term getPre(LocationVariable heap, Term heapTerm, Term selfTerm,
                             ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
                             Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public final Term getPre(List<LocationVariable> heapContext,
                             Map<LocationVariable, Term> heapTerms, Term selfTerm,
                             ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
                             Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public final Term getDep(LocationVariable heap, boolean atPre,
                             ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
                             Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                             Services services) {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public final Term getDep(LocationVariable heap, boolean atPre, Term heapTerm,
                             Term selfTerm, ImmutableList<Term> paramTerms,
                             Map<LocationVariable, Term> atPres, Services services) {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public final Term getGlobalDefs(LocationVariable heap, Term heapTerm, Term selfTerm,
                                    ImmutableList<Term> paramTerms, Services services) {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public final Term getMby(ProgramVariable selfVar,
                             ImmutableList<ProgramVariable> paramVars,
                             Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public final Term getMby(Map<LocationVariable,Term> heapTerms, Term selfTerm,
                             ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
                             Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    private final class TermListAndFunc {
        private final ImmutableList<Term> terms;
        private final Function func;

        private TermListAndFunc(ImmutableList<Term> ts, Function f) {
            this.terms = ts;
            this.func = f;
        }
    }

    final class Condition {
        private final Term implicit;
        private final Term explicit;

        Condition(Term implicit, Term explicit) {
            this.implicit = implicit;
            this.explicit = explicit;
        }
    }

    public final class TermAndFunc {
        public final Term term;
        public final Function func;

        TermAndFunc(Term t, Function f) {
            this.term = t;
            this.func = f;
        }
    }

    public final class POTerms {
        public final Condition pre;
        public final Term mod;
        public final ImmutableList<Term> rest;
        public final Condition post;

        POTerms(Condition pre, Term mod,
                ImmutableList<Term> rest, Condition post) {
            this.pre = pre;
            this.mod = mod;
            this.rest = rest;
            this.post = post;
        }
    }
}