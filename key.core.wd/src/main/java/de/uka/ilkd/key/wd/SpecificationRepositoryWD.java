/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.wd;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.*;

import org.key_project.util.collection.*;

import org.jspecify.annotations.NullMarked;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A special variant of
 *
 * @author Alexander Weigl
 * @version 1 (1/1/26)
 */
@NullMarked
public class SpecificationRepositoryWD extends SpecificationRepository {
    private static final Logger LOGGER = LoggerFactory.getLogger(SpecificationRepositoryWD.class);

    private final Map<Pair<KeYJavaType, IObserverFunction>, ImmutableSet<WellDefinednessCheck>> wdChecks =
        new LinkedHashMap<>();

    public SpecificationRepositoryWD(Services services) {
        super(services);
    }

    @Override
    protected void registerContract(Contract contract,
            Pair<KeYJavaType, IObserverFunction> targetPair) {
        LOGGER.trace("Contract registered {}", contract);
        if (!WellDefinednessCheck.isOn(services) && contract instanceof WellDefinednessCheck) {
            return;
        }
        super.registerContract(contract, targetPair);

        final KeYJavaType targetKJT = targetPair.first;
        final IObserverFunction targetMethod = targetPair.second;

        if (contract instanceof FunctionalOperationContract) {
            // Create new well-definedness check
            final MethodWellDefinedness mwd =
                new MethodWellDefinedness((FunctionalOperationContract) contract, services);
            registerContract(mwd, targetPair);
        } else if (contract instanceof DependencyContract && contract.getOrigVars().atPres.isEmpty()
                && Objects.equals(targetMethod.getContainerType(),
                    services.getJavaInfo().getJavaLangObject())) {
            // Create or extend a well-definedness check for a class invariant
            final JTerm deps =
                contract.getAccessible(services.getTypeConverter().getHeapLDT().getHeap());
            final JTerm mby = contract.getMby();
            final String invName = "JML model class invariant in " + targetKJT.getName();
            final ClassInvariant inv = new ClassInvariantImpl(invName, invName, targetKJT,
                contract.getVisibility(), tb.tt(), contract.getOrigVars().self);
            ClassWellDefinedness cwd =
                new ClassWellDefinedness(inv, targetMethod, deps, mby, services);
            final ImmutableSet<ClassWellDefinedness> cwds = getWdClassChecks(targetKJT);
            if (!cwds.isEmpty()) {
                assert cwds.size() == 1;
                final ClassWellDefinedness oldCwd = cwds.iterator().next();
                unregisterContract(oldCwd);
                oldCwd.addInv(cwd.getInvariant().getInv(oldCwd.getOrigVars().self, services));
                cwd = oldCwd.combine(cwd, services);
            }
            registerContract(cwd, targetPair);
        } else if (contract instanceof DependencyContract
                && contract.getOrigVars().atPres.isEmpty()) {
            // Create or extend a well-definedness check for a model field
            MethodWellDefinedness mwd =
                new MethodWellDefinedness((DependencyContract) contract, services);
            final ImmutableSet<MethodWellDefinedness> mwds =
                getWdMethodChecks(targetKJT, targetMethod);
            if (!mwds.isEmpty()) {
                assert mwds.size() == 1;
                final MethodWellDefinedness oldMwd = mwds.iterator().next();
                unregisterContract(oldMwd);
                mwd = mwd.combine(oldMwd, services);
            }
            registerContract(mwd, targetPair);
        } else if (contract instanceof WellDefinednessCheck) {
            registerWdCheck((WellDefinednessCheck) contract);
        }
        /*
         * contractsByName.put(contract.getName(), contract);
         * final ImmutableSet<IObserverFunction> oldTargets = getContractTargets(targetKJT);
         * final ImmutableSet<IObserverFunction> newTargets = oldTargets.add(targetMethod);
         * contractTargets.put(targetKJT, newTargets);
         */
    }


    /**
     * Remove well-definedness checks from a given set of contracts
     *
     * @param contracts A set of contracts
     * @return contracts without well-definedness checks
     */
    private static ImmutableSet<Contract> removeWdChecks(ImmutableSet<Contract> contracts) {
        ImmutableList<Contract> result = ImmutableSLList.nil();
        if (contracts == null) {
            return contracts;
        }
        for (Contract c : contracts) {
            if (!(c instanceof WellDefinednessCheck)) {
                result = result.prepend(c);
            }
        }
        return DefaultImmutableSet.fromImmutableList(result);
    }

    /**
     * Registers a well-definedness check. It does not take care of its visibility in the proof
     * management dialog (this is done in {@link #registerContract(Contract, Pair)}).
     *
     * @param check The well-definedness check to be registered
     */
    private void registerWdCheck(WellDefinednessCheck check) {
        ImmutableSet<WellDefinednessCheck> checks =
            getWdChecks(check.getKJT(), check.getTarget()).add(check);
        wdChecks.put(new Pair<>(check.getKJT(), check.getTarget()), checks);
    }

    /**
     * Unregisters a well-definedness check. It does not take care of its visibility in the proof
     * management dialog.
     *
     * @param check The well-definedness check to be unregistered
     */
    private void unregisterWdCheck(WellDefinednessCheck check) {
        wdChecks.put(new Pair<>(check.getKJT(), check.getTarget()),
            getWdChecks(check.getKJT(), check.getTarget()).remove(check));
    }

    /**
     * Returns all registered (atomic) well-definedness checks for the passed kjt.
     */
    private ImmutableSet<WellDefinednessCheck> getWdChecks(KeYJavaType kjt) {
        assert kjt != null;
        ImmutableSet<WellDefinednessCheck> result = DefaultImmutableSet.nil();
        for (WellDefinednessCheck ch : getAllWdChecks()) {
            if (ch.getKJT().equals(kjt)) {
                result = result.add(ch);
            }
        }
        return result;
    }

    /**
     * Returns all registered (atomic) well-definedness checks for the passed target and kjt.
     */
    private ImmutableSet<WellDefinednessCheck> getWdChecks(KeYJavaType kjt,
            IObserverFunction target) {
        assert kjt != null;
        assert target != null;
        target = getCanonicalFormForKJT(target, kjt);
        final Pair<KeYJavaType, IObserverFunction> pair = new Pair<>(kjt, target);
        final ImmutableSet<WellDefinednessCheck> result = wdChecks.get(pair);
        return result == null ? DefaultImmutableSet.nil() : result;
    }

    /**
     * Returns all registered well-definedness checks for method contracts.
     */
    private ImmutableSet<MethodWellDefinedness> getAllWdMethodChecks() {
        ImmutableSet<MethodWellDefinedness> result = DefaultImmutableSet.nil();
        for (var s : getAllWdChecks()) {
            if (s instanceof MethodWellDefinedness) {
                result = result.add((MethodWellDefinedness) s);
            }
        }
        return result;
    }

    /**
     * Returns all registered (atomic) well-definedness method checks for the passed kjt.
     */
    private ImmutableSet<MethodWellDefinedness> getWdMethodChecks(KeYJavaType kjt) {
        assert kjt != null;
        ImmutableSet<MethodWellDefinedness> result = DefaultImmutableSet.nil();
        for (MethodWellDefinedness ch : getAllWdMethodChecks()) {
            if (ch.getKJT().equals(kjt)) {
                result = result.add(ch);
            }
        }
        return result;
    }

    /**
     * Returns all registered (atomic) well-definedness method checks for the passed target and kjt.
     */
    private ImmutableSet<MethodWellDefinedness> getWdMethodChecks(KeYJavaType kjt,
            IObserverFunction target) {
        assert kjt != null;
        assert target != null;
        ImmutableSet<MethodWellDefinedness> result = DefaultImmutableSet.nil();
        for (MethodWellDefinedness ch : getAllWdMethodChecks()) {
            if (ch.getKJT().equals(kjt) && ch.getTarget().equals(target)) {
                result = result.add(ch);
            }
        }
        return result;
    }

    /**
     * Returns all registered (atomic) well-definedness class checks for the passed kjt.
     */
    private ImmutableSet<ClassWellDefinedness> getWdClassChecks(KeYJavaType kjt) {
        ImmutableSet<WellDefinednessCheck> checks = getWdChecks(kjt);
        ImmutableSet<ClassWellDefinedness> invs = DefaultImmutableSet.nil();
        for (WellDefinednessCheck check : checks) {
            if (check instanceof ClassWellDefinedness) {
                invs = invs.add((ClassWellDefinedness) check);
            }
        }
        return invs;
    }

    /**
     * Registers a well-definedness check for a jml statement. It does not take care of its
     * visibility in the proof management dialog.
     *
     * @param swd The well-definedness check
     */
    public void addWdStatement(StatementWellDefinedness swd) {
        registerWdCheck(swd);
    }

    /**
     * Returns all registered well-definedness checks.
     */
    public ImmutableSet<WellDefinednessCheck> getAllWdChecks() {
        ImmutableSet<WellDefinednessCheck> result = DefaultImmutableSet.nil();
        for (ImmutableSet<WellDefinednessCheck> s : wdChecks.values()) {
            result = result.union(s);
        }
        return result;
    }

    /**
     * Removes the contract from the repository, but keeps its target.
     */
    @Override
    protected void unregisterContract(Contract contract) {
        super.unregisterContract(contract);

        final KeYJavaType kjt = contract.getKJT();

        if (contract instanceof FunctionalOperationContract) {
            if (!getWdChecks(contract.getKJT(), contract.getTarget()).isEmpty()) {
                ImmutableSet<WellDefinednessCheck> wdcs =
                    getWdChecks(contract.getKJT(), contract.getTarget());
                for (WellDefinednessCheck wdc : wdcs) {
                    if (wdc instanceof MethodWellDefinedness
                            && ((MethodWellDefinedness) wdc).getMethodContract().equals(contract)) {
                        unregisterWdCheck(wdc);
                    }
                }
            }
        }

        if (contract instanceof WellDefinednessCheck) {
            unregisterWdCheck((WellDefinednessCheck) contract);
        }

    }

    @Override
    public void map(UnaryOperator<JTerm> op, Services services) {
        super.map(op, services);
        mapValueSets(wdChecks, op, services);
    }


    @Override
    public ImmutableSet<Contract> getAllContracts() {
        var result = super.getAllContracts();
        return WellDefinednessCheck.isOn(services) ? result : removeWdChecks(result);
    }

    @Override
    public ImmutableSet<Contract> getContracts(KeYJavaType kjt, IObserverFunction target) {
        var result = super.getContracts(kjt, target);
        if (WellDefinednessCheck.isOn(services))
            return result;
        else
            return removeWdChecks(result);
    }


    /**
     * Represent terms belong to model fields, so the well-definedness check considers both of them
     * together.
     *
     * @param kjt The relevant KeYJavaType
     */
    @Override
    public void processJavaType(KeYJavaType kjt) {
        ImmutableSet<ClassAxiom> axs = axioms.get(kjt);
        if (axs == null) {
            return;
        }
        ImmutableSet<RepresentsAxiom> reps = DefaultImmutableSet.nil();
        for (ClassAxiom ax : axs) {
            if (ax instanceof RepresentsAxiom) {
                reps = reps.add((RepresentsAxiom) ax);
            }
        }
        final ProgramVariable heap = services.getTypeConverter().getHeapLDT().getHeap();
        for (RepresentsAxiom rep : reps) {
            boolean dep = false;
            for (MethodWellDefinedness ch : getWdMethodChecks(kjt)) {
                if (ch.modelField() && ch.getTarget().equals(rep.getTarget())) {
                    dep = true;
                    unregisterContract(ch);
                    JTerm represents = rep.getAxiom(heap, ch.getOrigVars().self, services);
                    WellDefinednessCheck newCh = ch.addRepresents(represents);
                    registerContract(newCh);
                }
            }
            if (!dep) {
                MethodWellDefinedness mwd = new MethodWellDefinedness(rep, services);
                registerContract(mwd);
            }
        }
    }

    @Override
    public void addClassInvariant(ClassInvariant inv) {
        super.addClassInvariant(inv);

        final KeYJavaType kjt = inv.getKJT();
        final IObserverFunction target = inv.isStatic() ? services.getJavaInfo().getStaticInv(kjt)
                : services.getJavaInfo().getInv();

        final ImmutableSet<ClassWellDefinedness> cwds = getWdClassChecks(kjt);
        if (cwds.isEmpty()) {
            registerContract(new ClassWellDefinedness(inv, target, null, null, services));
        } else {
            assert cwds.size() == 1;
            ClassWellDefinedness cwd = cwds.iterator().next();
            unregisterContract(cwd);
            cwd = cwd.combine(new ClassWellDefinedness(inv, cwd.getTarget(), null, null, services),
                services);
            registerContract(cwd);
        }

        // inherit non-private, non-static invariants
        if (!inv.isStatic() && VisibilityModifier.allowsInheritance(inv.getVisibility())) {
            final ImmutableList<KeYJavaType> subs = services.getJavaInfo().getAllSubtypes(kjt);
            for (KeYJavaType sub : subs) {
                ClassInvariant subInv = inv.setKJT(sub);
                final IObserverFunction subTarget =
                    subInv.isStatic() ? services.getJavaInfo().getStaticInv(sub)
                            : services.getJavaInfo().getInv();
                final ImmutableSet<ClassWellDefinedness> subCwds = getWdClassChecks(sub);
                if (subCwds.isEmpty()) {
                    registerContract(
                        new ClassWellDefinedness(subInv, subTarget, null, null, services));
                } else {
                    for (ClassWellDefinedness cwd : subCwds) {
                        unregisterContract(cwd);
                        cwd.addInv(subInv.getInv(cwd.getOrigVars().self, services));
                        registerContract(cwd);
                    }
                }
            }
        }
    }

}
