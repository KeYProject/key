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

package de.uka.ilkd.key.gui.macros;

import java.util.Set;


public class HeapSimplificationMacro extends AbstractPropositionalExpansionMacro {

    @Override
    public String getName() {
        return "Heap Simplification";
    }

    @Override
    public String getDescription() {
        return "todo";
    }

    private static final String[] ADMITTED_RULES = {
        "selectOfStore",
        "selectOfCreate",
        "selectOfAnon",
        "selectOfMemset",
        
        "elementOfEmpty",
        "elementOfAllLocs",
        "elementOfSingleton",
        "elementOfUnion",
        "elementOfIntersect",
        "elementOfSetMinus",
        "elementOfAllFields",            
        "elementOfAllObjects",
        "elementOfArrayRange",
        "elementOfFreshLocs",
        "elementOfInfiniteUnion",
        "subsetToElementOf",
        "disjointToElementOf",
        "createdInHeapToElementOf",
        
        "selectOfStoreEQ",
        "selectOfCreateEQ",
        "selectOfAnonEQ",
        "selectOfMemsetEQ",
        
        "elementOfEmptyEQ",
        "elementOfAllLocsEQ",
        "elementOfSingletonEQ",
        "elementOfUnionEQ",
        "elementOfIntersectEQ",
        "elementOfSetMinusEQ",
        "elementOfAllFieldsEQ",            
        "elementOfAllObjectsEQ",
        "elementOfArrayRangeEQ",
        "elementOfFreshLocsEQ",
        "elementOfInfiniteUnionEQ",
//        "ifthenelse_split", "ifthenelse_split_for",
    };

    private static final Set<String> ADMITTED_RULES_SET = asSet(ADMITTED_RULES);

    @Override
    protected Set<String> getAdmittedRuleNames() {
        return ADMITTED_RULES_SET;
    }
}