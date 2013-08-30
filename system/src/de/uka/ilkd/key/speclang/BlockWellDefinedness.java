package de.uka.ilkd.key.speclang;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.WellDefinednessPO.Variables;

public class BlockWellDefinedness extends StatementWellDefinedness {

    private final BlockContract block;

    private BlockWellDefinedness(String name, int id, Type type, IObserverFunction target,
                                 LocationVariable heap, OriginalVariables origVars,
                                 Condition requires, Term assignable, Term accessible,
                                 Condition ensures, Term mby, Term rep, BlockContract block) {
        super(name, id, type, target, heap, origVars, requires,
              assignable, accessible, ensures, mby, rep);
        this.block = block;
    }

    public BlockWellDefinedness(BlockContract block, ImmutableSet<ProgramVariable> params,
                                Services services) {
        super(block.getName(), block.getBlock().getStartPosition().getLine(), block.getMethod(),
              block.getOrigVars().add(convertParams(params)), Type.BLOCK_CONTRACT, services);
        assert block != null;
        final LocationVariable h = getHeap();
        this.block = block;
        setRequires(block.getRequires(h));
        setAssignable(block.getAssignable(h), services);
        setEnsures(block.getEnsures(h));
    }

    public Term generatePO(ProgramVariable self, ProgramVariable exception,
                           ProgramVariable result, LocationVariable heap,
                           ProgramVariable heapAtPre, Term anonHeap,
                           ImmutableSet<ProgramVariable> ps,
                           Term leadingUpdate, Services services) {
        // wd(pre) & (pre & wf(anon) -> wd(mod) & {anon^mod}(wd(ppost)))

        ImmutableList<ProgramVariable> params = ImmutableSLList.<ProgramVariable>nil();
        for (ProgramVariable p: ps) {
            params = params.append(p);
        }
        final Map<LocationVariable, ProgramVariable> atPres =
                new LinkedHashMap<LocationVariable, ProgramVariable>();
        atPres.put(heap, heapAtPre);
        final Variables vars = new Variables(self, result, exception, atPres, params, heap, anonHeap);
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
                                                    TB.and(wdMod, uPost))));
        return poTerms;
    }

    public BlockContract getStatement() {
        return this.block;
    }

    @Override
    public boolean transactionApplicableContract() {
        return block.isTransactionApplicable();
    }

    @Override
    public Contract setID(int newId) {
        return new BlockWellDefinedness(getName(), newId, type(), getTarget(), getHeap(),
                                        getOrigVars(), getRequires(), getAssignable(),
                                        getAccessible(), getEnsures(), getMby(),
                                        getRepresents(), getStatement());
    }

    @Override
    public Contract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new BlockWellDefinedness(getName(), id(), type(), newPM, getHeap(),
                                        getOrigVars(), getRequires(), getAssignable(),
                                        getAccessible(), getEnsures(), getMby(),
                                        getRepresents(), getStatement().setTarget(newKJT, newPM));
    }

    @Override
    public String getTypeName() {
        return "Well-Definedness of " + block.getDisplayName();
    }

    @Override
    public VisibilityModifier getVisibility() {
        return block.getVisibility();
    }

    @Override
    public KeYJavaType getKJT() {
        return block.getKJT();
    }
}