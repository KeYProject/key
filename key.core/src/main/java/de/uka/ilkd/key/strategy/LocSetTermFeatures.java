/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.ldt.SetLDT;

import org.key_project.logic.op.Function;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

/// Term features for location sets
class LocSetTermFeatures extends SetTermFeatures {

    LocSetTermFeatures(SetLDT sets, LocSetLDT locSets, HeapLDT heaps) {
        super(sets);

        allLocs = locSets.getAllLocs();
        arrayRange = locSets.getArrayRange();
        allFields = locSets.getAllFields();
        allObjects = locSets.getAllObjects();
        arr = heaps.getArr();

        allLocsF = op(allLocs);
        arrayRangeF = op(arrayRange);
        allFieldsF = op(allFields);
        allObjectsF = op(allObjects);
        arrF = op(arr);

        requireLocationDecomposition = some(or(arrayRangeF, allFieldsF, allObjectsF, arrF));
    }

    final Function allLocs;
    final Function arrayRange;
    final Function allFields;
    final Function allObjects;
    final Function arr;

    final TermFeature allLocsF;
    final TermFeature arrayRangeF;
    final TermFeature allFieldsF;
    final TermFeature allObjectsF;
    final TermFeature arrF;

    /**
     * Axiomatisation or lemmas for these constructors require decomposition
     * of a location into its components
     */
    final TermFeature requireLocationDecomposition;
}
