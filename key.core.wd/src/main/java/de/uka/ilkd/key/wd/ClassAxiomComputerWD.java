/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.wd;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.declaration.ModifierKind;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.speclang.ClassAxiomComputer;
import de.uka.ilkd.key.speclang.ClassInvariant;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

/**
 * The well-definedness variant of the {@link ClassAxiomComputer}: registers the
 * {@link ClassWellDefinedness} checks that belong to newly added class invariants, mirroring the
 * invariant inheritance of the base implementation.
 */
public class ClassAxiomComputerWD extends ClassAxiomComputer {

    public ClassAxiomComputerWD(Services services) {
        super(services);
    }

    @Override
    public void addClassInvariant(ClassInvariant inv) {
        super.addClassInvariant(inv);

        final ContractRegistryWD specRepo =
            (ContractRegistryWD) services.getContractRegistry();
        final KeYJavaType kjt = inv.getKJT();
        final IObserverFunction target = inv.isStatic() ? services.getJavaInfo().getStaticInv(kjt)
                : services.getJavaInfo().getInv();

        final ImmutableSet<ClassWellDefinedness> cwds = specRepo.getWdClassChecks(kjt);
        if (cwds.isEmpty()) {
            specRepo.registerContractForClassAxioms(
                new ClassWellDefinedness(inv, target, null, null, services));
        } else {
            assert cwds.size() == 1;
            ClassWellDefinedness cwd = cwds.iterator().next();
            specRepo.unregisterContractForClassAxioms(cwd);
            cwd = cwd.combine(new ClassWellDefinedness(inv, cwd.getTarget(), null, null, services),
                services);
            specRepo.registerContractForClassAxioms(cwd);
        }

        // inherit non-private, non-static invariants
        if (!inv.isStatic() && ModifierKind.allowsInheritance(inv.getVisibility())) {
            final ImmutableList<KeYJavaType> subs = services.getJavaInfo().getAllSubtypes(kjt);
            for (KeYJavaType sub : subs) {
                ClassInvariant subInv = inv.setKJT(sub);
                final IObserverFunction subTarget =
                    subInv.isStatic() ? services.getJavaInfo().getStaticInv(sub)
                            : services.getJavaInfo().getInv();
                final ImmutableSet<ClassWellDefinedness> subCwds = specRepo.getWdClassChecks(sub);
                if (subCwds.isEmpty()) {
                    specRepo.registerContractForClassAxioms(
                        new ClassWellDefinedness(subInv, subTarget, null, null, services));
                } else {
                    for (ClassWellDefinedness cwd : subCwds) {
                        specRepo.unregisterContractForClassAxioms(cwd);
                        cwd.addInv(subInv.getInv(cwd.getOrigVars().self, services));
                        specRepo.registerContractForClassAxioms(cwd);
                    }
                }
            }
        }
    }
}
