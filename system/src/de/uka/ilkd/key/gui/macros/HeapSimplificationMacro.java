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
    
    private static final Set<String> ADMITTED_RULES_SET = asSet(new String[]{
        "selectOfStore",
        "selectOfCreate",
        "selectOfAnon",
        "selectOfMemset",
        
        "selectCreatedOfStore",
        "selectCreatedOfCreate",
        "selectCreatedOfAnon",
        "selectCreatedOfMemset",
        
        "dismissNonSelectedField",
        "dismissNonSelectedFieldEQ",
        
        // these are in ruleset concrete, but listed here to be applied when OSS is off
        "replaceKnownSelect",
        "dropEffectlessStores",
        "memsetEmpty",
        "selectCreatedOfAnonAsFormula",
        
        "wellFormedStoreObject",
        "wellFormedStoreArray",
        "wellFormedStorePrimitive",
        "wellFormedStorePrimitiveArray",
        "wellFormedStoreLocSet",
        "wellFormedCreate",
        "wellFormedAnon",
        "wellFormedMemsetArrayObject",
        "wellFormedMemsetArrayPrimitive",
        "wellFormedMemsetObject",
        "wellFormedMemsetLocSet",
        "wellFormedMemsetPrimitive",
        
        
        // EQ versions of the above
        // XXX do not really work....
        "selectOfStoreEQ",
        "selectOfCreateEQ",
        "selectOfAnonEQ",
        "selectOfMemsetEQ",
        
        "selectCreatedOfStoreEQ",
        "selectCreatedOfCreateEQ",
        "selectCreatedOfAnonEQ",
        "selectCreatedOfMemsetEQ",

        "wellFormedStoreObjectEQ",
        "wellFormedStoreArrayEQ",
        "wellFormedStorePrimitiveEQ",
        "wellFormedStorePrimitiveArrayEQ",
        "wellFormedStoreLocSetEQ",
        "wellFormedCreateEQ",
        "wellFormedAnonEQ",
        "wellFormedMemsetArrayObjectEQ",
        "wellFormedMemsetArrayPrimitiveEQ",
        "wellFormedMemsetObjectEQ",
        "wellFormedMemsetLocSetEQ",
        "wellFormedMemsetPrimitiveEQ",
        
        // locset rules
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
        "elementOfInfiniteUnion2Vars",
        
        "disjointDefinition", // TODO: may have own rules in future
        
        // TODO: add derived simplification rules
        
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
        "elementOfInfiniteUnion2VarsEQ",
        
        // others
        "nonNull",
        "nonNullZero",
        
        "allRight",
        "close",
        "closeTrue",
        "closeFalse"
    });


    @Override
    protected Set<String> getAdmittedRuleNames() {
        return ADMITTED_RULES_SET;
    }
    
    @Override
    protected boolean allowOSS () {
        return true;
    }
}