/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.wd;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.*; // NOPMD - type hierarchy

import org.key_project.util.collection.*;

/**
 * A special variant of
 *
 * @author Alexander Weigl
 * @version 1 (1/1/26)
 */
public class SpecificationRepositoryWD extends SpecificationRepository {

    public SpecificationRepositoryWD(Services services) {
        super(services);
    }

    /**
     * Represent terms belong to model fields, so the well-definedness check considers both of them
     * together.
     *
     * @param kjt The relevant KeYJavaType
     */
    @Override
    public void processJavaType(KeYJavaType kjt) {
        final ContractRegistryWD registry =
            (ContractRegistryWD) services.getContractRegistry();
        ImmutableSet<ClassAxiom> axs =
            services.getClassAxiomComputer().getClassAxiomsForType(kjt);
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
            for (MethodWellDefinedness ch : registry.getWdMethodChecks(kjt)) {
                if (ch.modelField() && ch.getTarget().equals(rep.getTarget())) {
                    dep = true;
                    registry.unregisterContractForClassAxioms(ch);
                    JTerm represents = rep.getAxiom(heap, ch.getOrigVars().self, services);
                    WellDefinednessCheck newCh = ch.addRepresents(represents);
                    registry.registerContractForClassAxioms(newCh);
                }
            }
            if (!dep) {
                MethodWellDefinedness mwd = new MethodWellDefinedness(rep, services);
                registry.registerContractForClassAxioms(mwd);
            }
        }
    }

}
