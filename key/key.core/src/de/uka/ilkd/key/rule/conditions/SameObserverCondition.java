// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.conditions;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.DependencyContract;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import java.util.Collections;


public final class SameObserverCondition implements VariableCondition {

	private final SchemaVariable schema1;
	private final SchemaVariable schema2;

	public SameObserverCondition(ParsableVariable schema1, ParsableVariable schema2) {
		try {
			this.schema1 = (SchemaVariable) schema1;
			this.schema2 = (SchemaVariable) schema2;
		} catch (ClassCastException e) {
			throw new RuntimeException("Arguments to \\sameObserver must be term SV", e);
		}
	}


	@Override
	public MatchConditions check(SchemaVariable var,
								 SVSubstitute instCandidate,
								 MatchConditions mc,
								 Services services) {
		SVInstantiations svInst = mc.getInstantiations();
		final Term term1 = (Term) svInst.getInstantiation(schema1);
		final Term term2 = (Term) svInst.getInstantiation(schema2);

		if ((term1 != null && !(term1.op() instanceof IObserverFunction)) ||
			(term2 != null && !(term2.op() instanceof IObserverFunction))) {
		      // if terms are present, they must be observer calls.
			return null;
		}

		if (term1 == null || term2 == null) {
			return mc;
		}

		IObserverFunction obs1 = (IObserverFunction) term1.op();
		IObserverFunction obs2 = (IObserverFunction) term2.op();

		if (obs1 != obs2) {
			return null;
		}

		if (obs1.getHeapCount(services) != 1 || obs1.getStateCount() != 1) {
			return null;
		}

        KeYJavaType kjt = obs1.isStatic() ?
                obs1.getContainerType() :
                services.getTypeConverter().getKeYJavaType(term1.sub(1));

        ImmutableSet<Contract> contracts =
                UseDependencyContractRule.getApplicableContracts(services, kjt, obs1);

        if (contracts == null || contracts.isEmpty()) {
            return null;
        }

        return mc;
	}


	@Override
		public String toString () {
			return "\\sameObserver (" + schema1 + ", " + schema2 + ")";
		}
	}