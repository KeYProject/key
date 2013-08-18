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
import de.uka.ilkd.key.logic.ImplicitSpecTermLabel;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
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

    private static final String INV_PREFIX = "wd Inv";
    private static final String OP_PREFIX = "wd Operation";

    private final String name;

    private final int id;

    private final Type type;

    private IObserverFunction target;

    private final LocationVariable heap;

    private Precondition requires;

    private Term assignable;

    private Term ensures;

    public static enum Type {
        CLASS_INVARIANT, CLASS_AXIOM, OPERATION_CONTRACT, LOOP_INVARIANT, BLOCK_CONTRACT;
    }

    Type type() {
        return this.type;
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof WellDefinednessCheck)) {
            return false;
        }
        WellDefinednessCheck wd = (WellDefinednessCheck)o;
        return wd.getName().equals(this.name);
    }

    @Override
    public int hashCode() {
        return this.name.hashCode();
    }

    public LocationVariable getHeap() {
        return this.heap;
    }

    public ImmutableList<LocationVariable> getHeaps() {
        ImmutableList<LocationVariable> result =
                ImmutableSLList.<LocationVariable>nil();
        return result.append(getHeap());
    }

    String typeString() {
        return type().toString().toLowerCase().replace("_", " ");
    }

    public Name name() {
        return new Name(getName());
    }

    @Override
    public String toString() {
        return getName();
    }

    WellDefinednessCheck(String name, int id, IObserverFunction target,
                         Type type, Services services) {
        this.id = id;
        this.name = name +" (wd)." + id;
        this.type = type;
        this.target = target;
        this.heap = services.getTypeConverter().getHeapLDT().getHeap();
    }

    WellDefinednessCheck(String name, int id, Type type, IObserverFunction target,
                         LocationVariable heap, Precondition requires,
                         Term assignable, Term ensures) {
        this.name = name;
        this.id = id;
        this.type = type;
        this.target = target;
        this.heap = heap;
        this.requires = requires;
        this.assignable = assignable;
        this.ensures = ensures;
    }

    @Override
    public String getName() {
        return this.name;
    }

    @Override
    public int id() {
        return id;
    }

    void setRequires(Term req) {
        Pair<Term, Term> requires = split(req);
        this.requires = new Precondition(requires.first, requires.second);
    }

    public Precondition getRequires() {
        assert this.requires != null;
        return this.requires;
    }

    void setAssignable(Term ass) {
        this.assignable = ass;
    }

    public Term getAssignable() {
        assert this.assignable != null;
        return this.assignable;
    }

    void setEnsures(Term ens) {
        Pair<Term, Term> ensures = split(ens);
        this.ensures = TB.andSC(ensures.first, ensures.second);
    }

    public Term getEnsures() {
        return this.ensures;
    }

    @Override
    public Term getRequires(LocationVariable heap) {
        return TB.andSC(getRequires().implicit, getRequires().explicit);
    }

    public Term getAssignable(LocationVariable heap) {
        return getAssignable();
    }

    @Override
    public String getHTMLText(Services services) {
        return getText(true, services);
    }

    @Override
    public String getPlainText(Services services) {
        return getText(false, services);
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
                String printPosts = LogicPrinter.quickPrintTerm(getEnsures(), services);
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
                    + (this instanceof MethodWellDefinedness ?
                            "<br><b>termination</b> " +
                            ((MethodWellDefinedness)this).getOperationContract().getModality()
                            : "")
                    + (transactionApplicableContract() ? "<br><b>transaction applicable</b>" : "") +
                    "</html>";

        }
        else {
            return sig.toString()
                    + pres
                    + posts
                    + mods
                    + (this instanceof MethodWellDefinedness ?
                            "\ntermination: " +
                            ((MethodWellDefinedness)this).getOperationContract().getModality()
                            : "")
                    + (transactionApplicableContract() ? "\ntransaction applicable:" : "");
        }
     }

    @Override
    public String proofToString(Services services) {
        assert false;
        return null;
    }

    @Override
    public IObserverFunction getTarget() {
        return this.target;
    }

    @Override
    public ProofOblInput createProofObl(InitConfig initConfig, Contract contract) {
        assert contract instanceof WellDefinednessCheck;
        return new WellDefinednessPO(initConfig, (WellDefinednessCheck) contract);
    }

    /** collects terms for precondition,
     * assignable clause and other specification elements,
     * and postcondition & signals-clause */
    abstract public POTerms createPOTerms();

    @Override
    public String getDisplayName() {
        return "Well-Definedness of JML " + typeString() + " " + id;
    }

    @Override
    public boolean toBeSaved() {
        return false;
    }

    private static Term removeImplicitSpecLabel(Term t) {
        ImmutableArray<ITermLabel> ls = t.getLabels();
        LinkedList<ITermLabel> res = new LinkedList<ITermLabel>();
        for (ITermLabel l: ls) {
            if(!l.equals(ImplicitSpecTermLabel.INSTANCE)) {
                res.add(l);
            }
        }
        if (res.isEmpty()) {
            ls = new ImmutableArray<ITermLabel>();
        } else {
            ls = new ImmutableArray<ITermLabel>(res);
        }
        res.clear();
        if (t.arity() > 0) {
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
                        && sub.getLabels().contains(ImplicitSpecTermLabel.INSTANCE)) {
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
        } else {
            if(spec.hasLabels()
                    && spec.getLabels().contains(ImplicitSpecTermLabel.INSTANCE)) {
                spec = removeImplicitSpecLabel(spec);
            }
            end = end.append(spec);
            return new Pair<ImmutableList<Term>, ImmutableList<Term>> (start, end);
        }
    }

    public Term replace(Term t, Variables vars) {
        return replace(t, vars, this);
    }

    public Precondition replace(Precondition pre, Variables vars) {
        final Term implicit = replace(pre.implicit, vars);
        final Term explicit = replace(pre.explicit, vars);
        return new Precondition(implicit, explicit);
    }

    public POTerms replace(POTerms po, Variables vars) {
        final Precondition pre = replace(po.pre, vars);
        final Term mod = replace(po.mod, vars);
        final ImmutableList<Term> rest = replace(po.rest, vars);
        final Term post = replace(po.post, vars);
        return new POTerms(pre, mod, rest, post);
    }

    public ImmutableList<Term> replace(Iterable<Term> l, Variables vars) {
        ImmutableList<Term> res = ImmutableSLList.<Term>nil();
        for (Term t: l) {
            res = res.append(replace(t, vars));
        }
        return res;
    }

    public Precondition replaceSelfSV(Precondition pre, SchemaVariable self) {
        final Term implicit = replaceSelfSV(pre.implicit, self);
        final Term explicit = replaceSelfSV(pre.explicit, self);
        return new Precondition(implicit, explicit);
    }

    public Term replaceSelfSV(Term t, SchemaVariable self) {
        return replaceSelfSV(t, self, this);
    }

    private static Term replaceSelfSV(Term t, SchemaVariable self,
                                      WellDefinednessCheck check) {
        return replaceSV(t, self, null, null, null, null,
                         check.getOrigVars(), check.getHeaps());
    }

    public static Term replace(Term t, Variables vars,
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
                                  ImmutableList<SchemaVariable> paramVars,
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

    private static Map<ProgramVariable,
                       SchemaVariable> getSchemaMap(SchemaVariable selfVar,
                                                    SchemaVariable resultVar,
                                                    SchemaVariable excVar,
                                                    Map<LocationVariable,
                                                        SchemaVariable> atPreVars,
                                                    ImmutableList<SchemaVariable> paramVars,
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
            final Iterator<SchemaVariable> it2 = paramVars.iterator();
            while(it1.hasNext()) {
                ProgramVariable originalParamVar = it1.next();
                SchemaVariable paramVar          = it2.next();
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

    private static Map<ProgramVariable,
                       ProgramVariable> getReplaceMap(ProgramVariable selfVar,
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

    private boolean isConstructor() {
        IObserverFunction target = getTarget();
        return target instanceof IProgramMethod
                && ((IProgramMethod)target).isConstructor();
    }

    private boolean isModel() {
        IObserverFunction target = getTarget();
        return target instanceof IProgramMethod
                && ((IProgramMethod)target).isModel();
    }

    private static Term[] getArgs(ParsableVariable pv,
                                  LocationVariable heap,
                                  boolean isStatic,
                                  ImmutableList<ProgramVariable> params,
                                  KeYJavaType kjt,
                                  Services services) {
        Term[] args = new Term[params.size() + (isStatic ? 1 : 2)];
        int i = 0;
        args[i++] = TB.var(heap);
        if (!isStatic) {
            args[i++] = TB.var(pv);
        }
        for (ProgramVariable arg : params) {
            args[i++] = TB.var(arg);
        }
        return args;
    }

    public Taclet createTaclet(String prefix,
                               Term var,
                               LocationVariable heap,
                               Term callTerm,
                               Term pre,
                               Services services) {
        final String refName;
        if (prefix.startsWith(INV_PREFIX) || isJavaLangObj(target)) {
            refName = target.getContainerType().getFullName();
        } else {
            refName = target.name().toString();
        }
        //final String baseName = getBaseName((ParsableVariable)calleeVar.op());
        final boolean isStatic = target.isStatic();
        final Name name =
                MiscTools.toValidTacletName(prefix
                        + (isStatic ? " Static " : " ")
                        + refName);
        final RewriteTacletBuilder tb = new RewriteTacletBuilder();
        final Term callee = var != null ?
                var : TB.var(SchemaVariableFactory.createTermSV(target.name(), target.sort()));
        final Term wdCallee = isStatic ? TB.tt() : TB.wd(callee, services);
        final Term wdHeap = TB.wd(TB.var(heap), services);
        final Term notNull = isStatic ?
                TB.tt() : TB.not(TB.equals(callee, TB.NULL(services)));
        final Term created = isStatic ? TB.tt() : TB.created(services, callee);
        tb.setFind(TB.wd(callTerm, services));
        tb.setName(name);
        tb.addRuleSet(new RuleSet(new Name("simplify")));
        tb.addGoalTerm(TB.andSC(notNull, wdCallee, wdHeap, created, pre));
        return tb.getTaclet();
    }

    public Taclet createInvTaclet(ProgramVariable pv,
                                  LocationVariable heap,
                                  Services services) {
        final KeYJavaType kjt = getKJT();
        boolean isStatic = target.isStatic();
        final Term[] heaps = new Term[] {TB.var(heap)};
        final SchemaVariable sv = target.isStatic() || pv == null ?
                SchemaVariableFactory.createTermSV(new Name("self"), kjt.getSort()) :
                    SchemaVariableFactory.createTermSV(pv.name(), kjt.getSort());
        final Term var = TB.var(sv);
        final Term invTerm = isStatic ?
                TB.staticInv(services, heaps, kjt) : TB.inv(services, heaps, var);
        return createTaclet(INV_PREFIX, var, heap, invTerm, TB.tt(), services);
    }

    public Taclet createOperationTaclet(ProgramVariable pv,
                                        Variables vars,
                                        Services services) {
        final boolean isStatic = getTarget().isStatic();
        final SchemaVariable sv;
        if (!isStatic) {
            sv = SchemaVariableFactory.createTermSV(
                    (pv != null ? pv.name() : new Name("callee")), getKJT().getSort());
        } else {
            sv = null;
        }
        final Term pre;
        if (vars.self == null) {
            pre = getPre(replaceSelfSV(getRequires(), sv), vars, sv, services).term;
        } else {
            pre = getPre(getRequires(), vars, services).term;
        }
        final Term[] args = getArgs(sv, vars.heap, isStatic,
                                    getOrigVars().params,
                                    getKJT(), services);
        final Term wdArgs = TB.and(TB.wd(args, services));
        return createTaclet(OP_PREFIX, (sv != null ? TB.var(sv): null), vars.heap,
                            TB.func(target, args), TB.and(wdArgs, pre), services);
    }

    private Term appendFreePre(Term pre,
                               ParsableVariable self,
                               LocationVariable heap,
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

    public Term[] getUpdates(Term mod, Variables vars, Services services) {
        assert mod != null;
        final Term havocUpd = TB.elementary(services, vars.heap,
                TB.anon(services, TB.var(vars.heap), mod, vars.anonHeap));
        final Term oldUpd = TB.elementary(services, TB.var(vars.heapAtPre), TB.var(vars.heap));
        return new Term[] {oldUpd, havocUpd};
    }

    public Term getPost(Term post, ProgramVariable result, Services services) {
        final Term implicit;
        if (result != null) {
            implicit = TB.reachableValue(services, result);
        } else {
            implicit = TB.tt();
        }
        return TB.andSC(implicit, post);
    }

    /**
     * Generates the general assumption that self is not null.
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @return The term representing the general assumption.
     */
    protected Term generateSelfNotNull(ProgramVariable selfVar,
                                       Services services) {
        return selfVar == null || isConstructor() ?
                TB.tt() : TB.not(TB.equals(TB.var(selfVar), TB.NULL(services)));
    }

    /**
     * Generates the general assumption that self is created.
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @return The term representing the general assumption.
     */
    protected Term generateSelfCreated(ProgramVariable selfVar,
                                              LocationVariable heap,
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
    protected Term generateSelfExactType(ProgramVariable selfVar,
                                                Services services) {
        final Term selfExactType = selfVar == null || isConstructor() ?
                TB.tt() :
                    TB.exactInstance(services, selfVar.getKeYJavaType().getSort(),
                                     TB.var(selfVar));
       return selfExactType;
    }

    /**
     * Generates the general assumption that all parameter arguments are valid.
     * @param paramVars The parameters {@link ProgramVariable}s.
     * @return The term representing the general assumption.
     */
    protected Term generateParamsOK(ImmutableList<ProgramVariable> paramVars,
                                    Services services) {
       Term paramsOK = TB.tt();
       for (ProgramVariable paramVar : paramVars) {
          paramsOK = TB.and(paramsOK, TB.reachableValue(services, paramVar));
       }
       return paramsOK;
    }

    protected Function generateMbyAtPre(Services services) {
        final FunctionalOperationContract foc;
        if (this instanceof MethodWellDefinedness) {
            foc = ((MethodWellDefinedness)this).getOperationContract();
        } else {
            foc = null;
        }
        if (foc != null && foc.hasMby()) {
            final Function mbyAtPreFunc =
                    new Function(new Name(TB.newName(services, "mbyAtPre")),
                                 services.getTypeConverter().getIntegerLDT().targetSort());
            return mbyAtPreFunc;
        } else {
            return null;
        }
    }

    protected Term generateMbyAtPre(ProgramVariable selfVar,
                                    ImmutableList<ProgramVariable> paramVars,
                                    Function mbyAtPreFunc,
                                    Services services) {
        if (mbyAtPreFunc != null) {
            assert this instanceof MethodWellDefinedness;
            FunctionalOperationContract foc =
                    ((MethodWellDefinedness)this).getOperationContract();
            final Term mbyAtPre = TB.func(mbyAtPreFunc);
            final Term mby = foc.getMby(selfVar, paramVars, services);
            return TB.equals(mbyAtPre, mby);
        } else {
            return TB.tt();
        }
    }

    protected TermAndFunc generateMbyAtPreDef(ProgramVariable selfVar,
                                              ImmutableList<ProgramVariable> paramVars,
                                              Services services) {
        final Function mbyAtPreFunc = generateMbyAtPre(services);
        final Term mbyAtPre = generateMbyAtPre(selfVar, paramVars, mbyAtPreFunc, services);
        return new TermAndFunc(mbyAtPre, mbyAtPreFunc);
    }

    /**
     * Builds the "general assumption" using the self variable (selfVar),
     * the {@link KeYJavaType} of the self variable (selfKJT),
     * the parameters {@link ProgramVariable}s (paramVars), the heaps (heaps), and
     * @param the implicit precondition
     * @return The {@link Term} containing the general assumptions.
     */
    protected TermListAndFunc buildFreePre(Term implicitPre,
                                           Variables vars,
                                           Services services) {
        ImmutableList<Term> resList = ImmutableSLList.<Term>nil();

        // "self != null"
        final Term selfNotNull = generateSelfNotNull(vars.self, services);

        // "self.<created> = TRUE"
        final Term selfCreated = generateSelfCreated(vars.self, heap, services);

        // "MyClass::exactInstance(self) = TRUE"
        final Term selfExactType = generateSelfExactType(vars.self, services);

        // conjunction of...
        // - "p_i = null | p_i.<created> = TRUE" for object parameters, and
        // - "inBounds(p_i)" for integer parameters
        Term paramsOK = generateParamsOK(vars.params, services);

        // initial value of measured_by clause
        final TermAndFunc mbyAtPreDef = generateMbyAtPreDef(vars.self, vars.params, services);
        final Term wellFormed = TB.wellFormed(heap, services);
        final Term[] result = new Term[]
                { wellFormed, selfNotNull, selfCreated, selfExactType,
                  implicitPre, paramsOK, mbyAtPreDef.term };
        for (Term t: result) {
            resList = resList.append(t);
        }
        return new TermListAndFunc(resList, mbyAtPreDef.func);
    }

    public TermAndFunc getPre(final Precondition pre,
                              Variables vars,
                              SchemaVariable self,
                              Services services) {
        final IObserverFunction target = getTarget();
        final TermListAndFunc freePre = buildFreePre(pre.implicit, vars, services);
        final ImmutableList<Term> preTerms = freePre.terms.append(pre.explicit);
        Term res = TB.andSC(preTerms);
        if ((target instanceof IProgramMethod
                && ((IProgramMethod)target).isConstructor()
                && !JMLInfoExtractor.isHelper((IProgramMethod)target))) {
            final Term constructorPre =
                    appendFreePre(res, self, vars.heap, services);
            return new TermAndFunc(constructorPre, freePre.func);
        } else {
            return new TermAndFunc(res, freePre.func);
        }
    }

    public TermAndFunc getPre(final Precondition pre,
                              Variables vars,
                              Services services) {
        final IObserverFunction target = getTarget();
        final TermListAndFunc freePre = buildFreePre(pre.implicit, vars, services);
        final ImmutableList<Term> preTerms = freePre.terms.append(pre.explicit);
        Term res = TB.andSC(preTerms);
        if ((target instanceof IProgramMethod
                && ((IProgramMethod)target).isConstructor()
                && !JMLInfoExtractor.isHelper((IProgramMethod)target))) {
            final Term constructorPre =
                    appendFreePre(res, vars.self, vars.heap, services);
            return new TermAndFunc(constructorPre, freePre.func);
        } else {
            return new TermAndFunc(res, freePre.func);
        }
    }

    private static boolean isJavaLangObj(IObserverFunction target) {
        return target.name().toString().startsWith("java.lang.Object");
    }

    @Deprecated
    public boolean hasMby() {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public Term getPre(LocationVariable heap, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars,
            Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public Term getPre(List<LocationVariable> heapContext,
                       ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
                       Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                       Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public Term getPre(LocationVariable heap, Term heapTerm, Term selfTerm,
                       ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
                       Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public Term getPre(List<LocationVariable> heapContext,
                       Map<LocationVariable, Term> heapTerms, Term selfTerm,
                       ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
                       Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public Term getGlobalDefs(LocationVariable heap, Term heapTerm, Term selfTerm,
                              ImmutableList<Term> paramTerms, Services services) {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public Term getMby(ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public Term getMby(Map<LocationVariable,Term> heapTerms, Term selfTerm,
                       ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
                       Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    public final class POTerms {
        public final Precondition pre;
        public final Term mod;
        public final ImmutableList<Term> rest;
        public final Term post;

        public POTerms(Precondition pre,
                       Term mod,
                       ImmutableList<Term> rest,
                       Term post) {
            this.pre = pre;
            this.mod = mod;
            this.rest = rest;
            this.post = post;
        }
    }

    public final class Precondition {
        public final Term implicit;
        public final Term explicit;

        Precondition(Term implicit,
                     Term explicit) {
            this.implicit = implicit;
            this.explicit = explicit;
        }
    }

    public final class TermAndFunc {
        public final Term term;
        public final Function func;

        TermAndFunc(Term t,
                    Function f) {
            this.term = t;
            this.func = f;
        }
    }

    public final class TermListAndFunc {
        public final ImmutableList<Term> terms;
        public final Function func;

        TermListAndFunc(ImmutableList<Term> ts,
                        Function f) {
            this.terms = ts;
            this.func = f;
        }
    }
}