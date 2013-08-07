package de.uka.ilkd.key.speclang;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.AutoSpecTermLabel;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.TransformerProcedure;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.WellDefinednessPO;
import de.uka.ilkd.key.util.Triple;

/**
 * A contract for checking the well-definedness of a specification element
 * (i.e. a class invariant, a method contract, a loop invariant or a block contract),
 * consisting of invariant/precondition (depending on which kind of contract it is)
 * and assignable-clause.
 */
/**
 * @author kirsten
 *
 */
public abstract class WellDefinednessCheck implements Contract {

    protected static final TermBuilder TB = TermBuilder.DF;
    protected static final TermFactory TF = TermFactory.DEFAULT;


    public final Type type;

    private IObserverFunction target;

    final LocationVariable heap;

    Term requires;

    Term assignable;

    Term ensures;

    public static enum Type {
        CLASS_INVARIANT, CLASS_AXIOM, METHOD_CONTRACT, LOOP_INVARIANT, BLOCK_CONTRACT;
    }

    Type type() {
        return type;
    }

    String typeString() {
        return type().toString().toLowerCase();
    }

    WellDefinednessCheck(IObserverFunction target, Type type, Services services) {
        this.type = type;
        this.target = target;
        this.heap = services.getTypeConverter().getHeapLDT().getHeap();
    }

    public Term getRequires() {
        assert this.requires != null;
        return this.requires;
    }

    public Term getAssignable() {
        assert this.assignable != null;
        return this.assignable;
    }

    public Term getEnsures() {
        return this.ensures;
    }

    public Term getRequires(LocationVariable heap) {
        return getRequires();
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

        if (includeHtmlMarkup) {
           return "<html>"
                 + pres
                 + mods +
                 "</html>";
        }
        else {
           return pres
                 + mods;
        }
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

    /* collects terms for precondition, other specification elements and postcondition &
     * signals-clause */
    abstract public Triple<Term, ImmutableList<Term>, Term> createPOTerm();

    @Override
    public String getDisplayName() {
        return "Well-Definedness of JML " + typeString();
    }

    @Override
    public boolean toBeSaved() {
        return false;
    }

    static Term relabel(Term t) {
        ImmutableArray<ITermLabel> ls = t.getLabels();
        LinkedList<ITermLabel> res = new LinkedList<ITermLabel>();
        for (ITermLabel l: ls) {
            if(!l.equals(AutoSpecTermLabel.INSTANCE)) {
                res.add(l);
            }
        }
        if (res.isEmpty()) {
            ls = new ImmutableArray<ITermLabel>();
        } else {
            ls = new ImmutableArray<ITermLabel>(res);
        }
        res.clear();
        return TB.relabel(t, ls);
    }

    public static Term wd(Term t, Services services) {
        if (new Name("Formula").equals(t.sort().name())) {
            return TB.func(wdFormula(services), t);
        } else {
            return TB.func(wdAny(services), t);
        }
    }

    static TransformerProcedure getTransformer(String nameString, Sort argSort, Services services) {
        Name name = new Name(nameString);
        Named f = services.getNamespaces().functions().lookup(name);
        if (f != null && f instanceof TransformerProcedure) {
            return (TransformerProcedure) f;
        } else {
            return new TransformerProcedure(name, Sort.FORMULA, argSort);
        }
    }

    static TransformerProcedure wdFormula(Services services) {
        return getTransformer("WD", Sort.FORMULA, services);
    }

    static TransformerProcedure wdAny(Services services) {
        return getTransformer("wd", Sort.ANY, services);
    }

    @Deprecated
    public boolean hasMby() {
        return false;
    }

    @Deprecated
    public Contract setTarget(KeYJavaType newKJT,
                              IObserverFunction newPM) throws UnsupportedOperationException {
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
}