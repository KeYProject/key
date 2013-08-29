package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.WellDefinednessPO.Variables;

public class LoopWellDefinedness extends WellDefinednessCheck {

    private final LoopInvariant inv;

    private LoopWellDefinedness(String name, int id, Type type, IObserverFunction target,
                                LocationVariable heap, OriginalVariables origVars,
                                Condition requires, Term assignable, Term accessible,
                                Condition ensures, Term mby, Term rep, LoopInvariant inv) {
        super(name, id, type, target, heap, origVars, requires,
              assignable, accessible, ensures, mby, rep);
        this.inv = inv;
    }

    public LoopWellDefinedness(LoopInvariant inv, ImmutableSet<ProgramVariable> params,
                               Services services) {
        super(ContractFactory.generateContractTypeName(inv.getName(),
                                                       inv.getKJT(),
                                                       inv.getTarget(),
                                                       inv.getKJT()),
              inv.getLoop().getStartPosition().getLine(), inv.getTarget(),
              new OriginalVariables(inv.getOrigVars().self, null, null,
                                    inv.getOrigVars().atPres, convertParams(params)),
              Type.LOOP_INVARIANT, services);
        assert inv != null;
        final LocationVariable h = getHeap();
        this.inv = inv;
        setMby(inv.getInternalVariant());
        setRequires(inv.getInternalInvariants().get(h));
        setAssignable(inv.getInternalModifies().get(h), services);
        setEnsures(inv.getInternalInvariants().get(h));
    }

    private static ImmutableList<ProgramVariable> convertParams(ImmutableSet<ProgramVariable> set) {
        ImmutableList<ProgramVariable> list = ImmutableSLList.<ProgramVariable>nil();
        for (ProgramVariable pv: set) {
            list = list.append(pv);
        }
        return list;
    }

    @Override
    TermAndFunc generateMbyAtPreDef(ParsableVariable self,
            ImmutableList<ParsableVariable> params, Services services) {
        return new TermAndFunc(TB.tt(), null);
    }

    @Override
    ImmutableList<Term> getRest() {
        return super.getRest();
    }

    public Term generatePO(ProgramVariable self, LocationVariable heap,
                           Term anonHeap, ImmutableSet<ProgramVariable> ps,
                           Term leadingUpdate, Services services) {
        // wd(phi) & (phi & wf(anon) -> wd(mod) & wd(variant) & {anon^mod}(wd(phi) & wd(variant)))

        ImmutableList<ProgramVariable> params = ImmutableSLList.<ProgramVariable>nil();
        for (ProgramVariable p: ps) {
            params = params.append(p);
        }
        final Variables vars = new Variables(self, null, null, null, params, heap, anonHeap);
        final POTerms po =
                replace(new POTerms(this.getRequires(), this.getAssignable(),
                                    this.getRest(), this.getEnsures()),
                        vars);
        final Term pre = getPre(po.pre, self, heap, params, false, services).term;
        final Term post = getPost(po.post, vars.result, services);
        final Term wdPre = TB.wd(pre, services);
        final Term wdMod = TB.wd(po.mod, services);
        final ImmutableList<Term> wdRest = TB.wd(po.rest, services);
        final Term updates = getUpdates(po.mod, heap, heap, anonHeap, services);
        final Term wfAnon = TB.wellFormed(anonHeap, services);
        final Term uPost = TB.apply(updates, TB.and(TB.wd(post, services), TB.and(wdRest)));
        final Term poTerms = TB.apply(leadingUpdate,
                                      TB.and(wdPre,
                                             TB.imp(TB.and(pre, wfAnon),
                                                    TB.and(wdMod, TB.and(wdRest), uPost))));
        return poTerms;
    }

    public LoopInvariant getInvariant() {
        return this.inv;
    }

    @Override
    public String getBehaviour() {
        return "";
    }

    @Override
    public Term getGlobalDefs() {
        throw new UnsupportedOperationException("Not applicable for well-definedness of loops.");
    }

    @Override
    public boolean transactionApplicableContract() {
        return false;
    }

    @Override
    public Contract setID(int newId) {
        return new LoopWellDefinedness(getName(), newId, type(), getTarget(), getHeap(),
                                       getOrigVars(), getRequires(), getAssignable(),
                                       getAccessible(), getEnsures(), getMby(),
                                       getRepresents(), getInvariant());
    }

    @Override
    public Contract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new LoopWellDefinedness(getName(), id(), type(), newPM, getHeap(),
                                       getOrigVars(), getRequires(), getAssignable(),
                                       getAccessible(), getEnsures(), getMby(),
                                       getRepresents(), getInvariant().setTarget(newKJT, newPM));
    }

    @Override
    public String getTypeName() {
        return "Well-Definedness of " + inv.getDisplayName();
    }

    @Override
    public VisibilityModifier getVisibility() {
        return inv.getVisibility();
    }

    @Override
    public KeYJavaType getKJT() {
        return inv.getKJT();
    }

    @Override
    public boolean isModel() {
        return false;
    }
}