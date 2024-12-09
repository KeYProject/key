/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.Set;

/**
 * This macro performs simplification of Heap and LocSet terms. It applies simplification rules
 * (including the "unoptimized" select rules), One Step Simplification, alpha, and delta rules.
 *
 * @author bruns
 *
 */
public class HeapSimplificationMacro extends AbstractPropositionalExpansionMacro {

    @Override
    public String getName() {
        return "Heap Simplification";
    }

    @Override
    public String getCategory() {
        return "Simplification";
    }

    @Override
    public String getScriptCommandName() {
        return "simp-heap";
    }

    @Override
    public String getDescription() {
        return "This macro performs simplification of Heap and LocSet terms.\n"
            + "It applies simplification rules (including the \"unoptimized\" select rules), "
            + "One Step Simplification, alpha, and delta rules.";
    }

    // note that rules in the 'concrete' rule set are usually not included here
    private static final Set<String> ADMITTED_RULES_SET = asSet("selectOfStore",
        "selectOfCreate", "selectOfAnon", "selectOfMemset",

        "selectCreatedOfStore", "selectCreatedOfCreate", "selectCreatedOfAnon",
        "selectCreatedOfMemset",

        "dismissNonSelectedField", "dismissNonSelectedFieldEQ", "replaceKnownSelect",
        "dropEffectlessStores", "memsetEmpty", "selectCreatedOfAnonAsFormula",

        "wellFormedStoreObject", "wellFormedStoreArray", "wellFormedStorePrimitive",
        "wellFormedStorePrimitiveArray", "wellFormedStoreLocSet", "wellFormedCreate",
        "wellFormedAnon", "wellFormedMemsetArrayObject", "wellFormedMemsetArrayPrimitive",
        "wellFormedMemsetObject", "wellFormedMemsetLocSet", "wellFormedMemsetPrimitive",


        // EQ versions of the above
        "selectOfStoreEQ", "selectOfCreateEQ", "selectOfAnonEQ", "selectOfMemsetEQ",

        "selectCreatedOfStoreEQ", "selectCreatedOfCreateEQ", "selectCreatedOfAnonEQ",
        "selectCreatedOfMemsetEQ",

        "wellFormedStoreObjectEQ", "wellFormedStoreArrayEQ", "wellFormedStorePrimitiveEQ",
        "wellFormedStorePrimitiveArrayEQ", "wellFormedStoreLocSetEQ", "wellFormedCreateEQ",
        "wellFormedAnonEQ", "wellFormedMemsetArrayObjectEQ", "wellFormedMemsetArrayPrimitiveEQ",
        "wellFormedMemsetObjectEQ", "wellFormedMemsetLocSetEQ", "wellFormedMemsetPrimitiveEQ",

        // locset rules
        "elementOfEmpty", "elementOfAllLocs", "elementOfSingleton", "elementOfUnion",
        "elementOfIntersect", "elementOfSetMinus", "elementOfAllFields", "elementOfAllObjects",
        "elementOfArrayRange", "elementOfFreshLocs", "elementOfInfiniteUnion",
        "elementOfInfiniteUnion2Vars",

        "allFieldsEq", "subsetSingletonLeft", "subsetSingletonLeftEQ", "subsetSingletonRight",
        "subsetSingletonRightEQ", "subsetUnionLeft", "subsetUnionLeftEQ",
        "subsetOfIntersectWithItSelfEQ1", "subsetOfIntersectWithItSelfEQ2", "allFieldsSubsetOf",
        "disjointAllFields", "disjointAllObjects", "disjointInfiniteUnion",
        "disjointInfiniteUnion_2", "intersectAllFieldsFreshLocs", "disjointWithSingleton1",
        "disjointWithSingleton2", "sortsDisjointModuloNull",

        "createdInHeapWithSingleton", "createdInHeapWithAllFields", "createdInHeapWithArrayRange",
        "createdInHeapWithSingletonEQ", "createdInHeapWithUnionEQ",
        "createdInHeapWithSetMinusFreshLocsEQ", "createdInHeapWithAllFieldsEQ",
        "createdInHeapWithArrayRangeEQ", "createdInHeapWithSelectEQ", "createdInHeapWithObserverEQ",

        "elementOfEmptyEQ", "elementOfAllLocsEQ", "elementOfSingletonEQ", "elementOfUnionEQ",
        "elementOfIntersectEQ", "elementOfSetMinusEQ", "elementOfAllFieldsEQ",
        "elementOfAllObjectsEQ", "elementOfArrayRangeEQ", "elementOfFreshLocsEQ",
        "elementOfInfiniteUnion2VarsEQ",

        // rules listed under "other lemma"
        "unionEqualsEmpty", "unionEqualsEmptyEQ", "intersectWithSingleton", "setMinusSingleton",
        "unionIntersectItself", "unionIntersectItself_2", "unionIntersectItself_3",
        "unionIntersectItself_4", "unionIntersectItself_5", "unionIntersectItself_6",

        // normalization rules are currently not included

        // semantics blasting rules
        // "equalityToElementOfRight",
        // "subsetToElementOfRight",
        "disjointDefinition", // TODO: may have own rules in future
        "definitionAllElementsOfArray", "definitionAllElementsOfArrayLocsets",

        // alpha rules
        "impRight", "andLeft", "orRight", "close", "closeTrue", "closeFalse", "ifthenelse_negated",
        // TODO: those must be more expensive
        // "replace_known_left",
        // "replace_known_right",

        // others
        "castDel", "nonNull", "nonNullZero", "allRight", "exLeft");


    @Override
    protected Set<String> getAdmittedRuleNames() {
        return ADMITTED_RULES_SET;
    }

    @Override
    protected boolean allowOSS() {
        return true;
    }
}
