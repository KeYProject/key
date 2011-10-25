// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGenerator;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

/**
 * A class axiom which is essentially of the form "o.<inv> -> phi": it demands
 * that the invariants of the objects of a particular class imply a particular
 * formula. These axioms are logically weaker than the full definitions of <inv>
 * expressed as RepresentsAxioms, but they may have higher visibility, making
 * them available in proofs where the corresponing full definition is not.
 */
public final class PartialInvAxiom extends ClassAxiom {
    
    private final ClassInvariant inv;
    private final ObserverFunction target;
    
    public PartialInvAxiom(ClassInvariant inv, Services services) {
	assert inv != null;
	this.inv = inv;
	this.target = services.getJavaInfo().getInv();
	assert target != null;
    }
    
    public PartialInvAxiom(ClassInvariant inv, String displayName, Services services){
        this(inv, services);
        this.displayName = displayName;
    }
    
    @Override
    public String getName() {
	return inv.getName();
    }

    
    @Override
    public ObserverFunction getTarget() {
	return target;
    }
    

    @Override
    public KeYJavaType getKJT() {
	return inv.getKJT();
    }
    
    
    @Override
    public VisibilityModifier getVisibility() {
	return inv.getVisibility();
    }
    
    
    @Override
    public ImmutableSet<Taclet> getTaclets(
            ImmutableSet<Pair<Sort, ObserverFunction>> toLimit,
            Services services) {
        ImmutableSet<Taclet> result = DefaultImmutableSet.<Taclet>nil();

        for (int i = 0; i < 2; i++) {
            TacletGenerator TG = TacletGenerator.getInstance();
            Name name = MiscTools.toValidTacletName("Partial inv axiom for "
                                                    + inv.getName()
                                                    + (i == 0 ? "" : " EQ"));
            ImmutableSet<Taclet> taclets =
                    TG.generatePartialInvTaclet(name,
                                                inv.getOriginalInv(),
                                                inv.getKJT(),
                                                toLimit,
                                                target.isStatic(),
                                                i == 1,
                                                services);
            result = result.union(taclets);

            //EQ taclet only for non-static invariants
            if (target.isStatic()) {
                break;
            }
        }

        //return
        return result;
    }
    
    
    @Override
    public ImmutableSet<Pair<Sort, ObserverFunction>> getUsedObservers(
	    						Services services) {
	final ProgramVariable dummySelfVar 
		= TB.selfVar(services, inv.getKJT(), false);
	return MiscTools.collectObservers(inv.getInv(dummySelfVar, services));
    }
    
    
    @Override
    public String toString() {
	return inv.toString();
    }
}
