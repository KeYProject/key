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

/**
 * This macro performs simplification of Heap and LocSet terms.
 * It applies simplification rules (including the "unoptimized" select rules),
 * One Step Simplification, alpha, and delta rules.
 * Currently all rules (except OSS) have zero costs.
 * @author bruns
 *
 */
public class HeapSimplificationMacro extends AbstractPropositionalExpansionMacro {

    @Override
    public String getName() {
        return "Heap Simplification";
    }

    @Override
    public String getDescription() {
        return "This macro performs simplification of Heap and LocSet terms.\n"
                    +"It applies simplification rules (including the \"unoptimized\" select rules), "
                    +"One Step Simplification, alpha, and delta rules.";
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
        
        "allFieldsEq",
        "subsetSingletonRight",
        "subsetSingletonRightEQ",
        "subsetOfIntersectWithItSelfEQ1",
        "subsetOfIntersectWithItSelfEQ2",
        "allFieldsSubsetOf",
        "disjointAllFields",
        "disjointAllObjects",
        "disjointInfiniteUnion",
        "disjointInfiniteUnion_2",
        "intersectAllFieldsFreshLocs",
        
        "createdInHeapWithSingleton",
        "createdInHeapWithAllFields",
        "createdInHeapWithArrayRange",
        "createdInHeapWithSingletonEQ",
        "createdInHeapWithUnionEQ",
        "createdInHeapWithSetMinusFreshLocsEQ",
        "createdInHeapWithAllFieldsEQ",
        "createdInHeapWithArrayRangeEQ",
        "createdInHeapWithSelectEQ",
        "createdInHeapWithObserverEQ",
        
        // TODO: the "other lemma" locset rules are not yet here
        
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
        
        // semantics blasting rules
        "equalityToElementOfRight",
        "subsetToElementOfRight",
        "disjointDefinition", // TODO: may have own rules in future
        
        // alpha rules
        "impRight",
        "andLeft",
        "orRight",
        "close",
        "closeTrue",
        "closeFalse",
        // TODO: those must be more expensive
//        "replace_known_left",
//        "replace_known_right",
        
        // others
        "nonNull",
        "nonNullZero",
        "allRight",
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