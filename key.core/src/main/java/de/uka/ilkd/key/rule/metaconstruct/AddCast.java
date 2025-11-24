/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;


public final class AddCast extends AbstractTermTransformer {

    public AddCast() {
        super(new Name("#addCast"), 2);
    }


    @Override
    public JTerm transform(JTerm term, SVInstantiations svInst, Services services) {
        JTerm sub = term.sub(0);
        Sort sort = term.sub(1).sort();

        return sub.sort().extendsTrans(sort) ? sub : services.getTermBuilder().cast(sort, sub);
    }
}
