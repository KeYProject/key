package de.uka.ilkd.key.speclang;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ImplicitSpecTermLabel;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.TransformerProcedure;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.WellDefinednessPO;
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
    public static Name WD_FORMULA = new Name("WD");
    public static Name WD_ANY = new Name("wd");

    private final String name;

    private final int id;

    private final Type type;

    private IObserverFunction target;

    private final LocationVariable heap;

    private Precondition requires;

    private Term assignable;

    private Term ensures;

    public static enum Type {
        CLASS_INVARIANT, CLASS_AXIOM, METHOD_CONTRACT, LOOP_INVARIANT, BLOCK_CONTRACT;
    }

    Type type() {
        return type;
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof WellDefinednessCheck)) {
            return false;
        }
        WellDefinednessCheck wd = (WellDefinednessCheck)o;
        return wd.getName().equals(name);
    }

    @Override
    public int hashCode() {
        return name.hashCode();
    }

    public LocationVariable getHeap() {
        return this.heap;
    }

    private List<LocationVariable> getHeaps() {
        List<LocationVariable> result = new ArrayList<LocationVariable>(1);
        result.add(getHeap());
        return result;
    }

    String typeString() {
        return type().toString().toLowerCase();
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
        Pair<Term, Term> requires = sortAndShortcut(req);
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
        Pair<Term, Term> ensures = sortAndShortcut(ens);
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
        sig.append(isPM() ? ((IProgramMethod)target).getName() : "");
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
        return target;
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

    private static Term relabel(Term t) {
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
                subs[i++] = relabel(sub);
            }
            t = TF.createTerm(t.op(), subs, t.getLabels());
        }
        return TB.relabel(t, ls);
    }

    public static Term wd(Term t, Services services) {
        if (new Name("Formula").equals(t.sort().name())) {
            return TB.func(wdFormula(services), t);
        } else {
            return TB.func(wdAny(services), t);
        }
    }

    private static TransformerProcedure wdFormula(Services services) {
        return TransformerProcedure.getTransformer(WD_FORMULA, Sort.FORMULA, services);
    }

    private static TransformerProcedure wdAny(Services services) {
        return TransformerProcedure.getTransformer(WD_ANY, Sort.ANY, services);
    }

    private static Pair<Term, Term> sortAndShortcut(Term spec) {
        Pair<ImmutableList<Term>, ImmutableList<Term>> p = sort(spec);
        ImmutableList<Term> start = p.first;
        ImmutableList<Term> end   = p.second;
        return new Pair<Term, Term> (TB.andSC(start), TB.andSC(end));
    }

    private static Pair<ImmutableList<Term>, ImmutableList<Term>> sort(Term spec) {
        assert spec != null;
        ImmutableList<Term> start = ImmutableSLList.<Term>nil();
        ImmutableList<Term> end = ImmutableSLList.<Term>nil();
        if(spec.arity() > 0
                && spec.op().equals(Junctor.AND)) {
            for (Term sub: spec.subs()) {
                if(sub.hasLabels()
                        && sub.getLabels().contains(ImplicitSpecTermLabel.INSTANCE)) {
                    sub = relabel(sub);
                    Pair<ImmutableList<Term>, ImmutableList<Term>> p = sort(sub);
                    start = start.append(p.first).append(p.second);
                } else {
                    Pair<ImmutableList<Term>, ImmutableList<Term>> p = sort(sub);
                    start = start.append(p.first);
                    end = end.append(p.second);
                }
            }
            return new Pair<ImmutableList<Term>, ImmutableList<Term>> (start, end);
        } else {
            if(spec.hasLabels()
                    && spec.getLabels().contains(ImplicitSpecTermLabel.INSTANCE)) {
                spec = relabel(spec);
            }
            end = end.append(spec);
            return new Pair<ImmutableList<Term>, ImmutableList<Term>> (start, end);
        }
    }

    public Term replace(Term t,
                        ProgramVariable selfVar,
                        ProgramVariable resultVar,
                        ProgramVariable excVar,
                        Map<LocationVariable,
                            ProgramVariable> atPreVars,
                        ImmutableList<ProgramVariable> paramVars) {
        Map<ProgramVariable, ProgramVariable> map =
                getReplaceMap(selfVar, resultVar, excVar, atPreVars,
                              paramVars, getOrigVars(), getHeaps());
        final OpReplacer or = new OpReplacer(map);
        return or.replace(t);
    }

    private static Map<ProgramVariable,
                       ProgramVariable> getReplaceMap(ProgramVariable selfVar,
                                                      ProgramVariable resultVar,
                                                      ProgramVariable excVar,
                                                      Map<LocationVariable,
                                                          ProgramVariable> atPreVars,
                                                      ImmutableList<ProgramVariable> paramVars,
                                                      OriginalVariables vars,
                                                      List<LocationVariable> heaps) {
        final Map<ProgramVariable, ProgramVariable> result =
                new LinkedHashMap<ProgramVariable, ProgramVariable>();

        //self
        if(selfVar != null) {
            assert selfVar.sort().extendsTrans(vars.self.sort());
            result.put(vars.self, selfVar);
        }

        //parameters
        if(paramVars != null) {
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
        if(resultVar != null) {
            assert vars.result.sort().equals(resultVar.sort());
            result.put(vars.result, resultVar);
        }

        //exception
        if(excVar != null) {
            assert vars.exception.sort().equals(excVar.sort());
            result.put(vars.exception, excVar);
        }

        if(atPreVars != null) {
            for(LocationVariable h : heaps) {
                if(atPreVars.get(h) != null) {
                    assert vars.atPres.get(h).sort().equals(atPreVars.get(h).sort());
                    result.put(vars.atPres.get(h), atPreVars.get(h));
                }
            }
        }

        return result;
    }

    private boolean isPM() {
        return target instanceof IProgramMethod;
    }

    private boolean isConstructor() {
        return isPM() && ((IProgramMethod)target).isConstructor();
    }

    private boolean isModel() {
        return isPM() && ((IProgramMethod)target).isModel();
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

        public Precondition(Term implicit,
                            Term explicit) {
            this.implicit = implicit;
            this.explicit = explicit;
        }
    }
}