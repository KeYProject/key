/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.ldt.SetLDT;
import de.uka.ilkd.key.logic.op.ParametricFunctionDecl;

import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

/// Term features for the theory of sets.
public class SetTermFeatures extends StaticFeatureCollection {

    SetTermFeatures(SetLDT sets) {
        empty = sets.getEmpty();
        singleton = sets.getSingleton();
        union = sets.getUnion();
        intersect = sets.getIntersect();
        setMinus = sets.getSetMinus();
        infiniteUnion = sets.getInfiniteUnion();
        card = sets.getCard();
        elementOf = sets.getElementOf();
        subset = sets.getSubset();
        disjoint = sets.getDisjoint();

        emptyF = opBase(empty);
        singletonF = opBase(singleton);
        unionF = opBase(union);
        intersectF = opBase(intersect);
        setMinusF = opBase(setMinus);
        infiniteUnionF = opBase(infiniteUnion);
        cardF = opBase(card);
        elementOfF = opBase(elementOf);
        subsetF = opBase(subset);
        disjointF = opBase(disjoint);
    }

    public final ParametricFunctionDecl empty;
    public final ParametricFunctionDecl singleton;
    public final ParametricFunctionDecl union;
    public final ParametricFunctionDecl intersect;
    public final ParametricFunctionDecl setMinus;
    public final ParametricFunctionDecl infiniteUnion;
    public final ParametricFunctionDecl card;
    public final ParametricFunctionDecl elementOf;
    public final ParametricFunctionDecl subset;
    public final ParametricFunctionDecl disjoint;

    final TermFeature emptyF;
    final TermFeature singletonF;
    final TermFeature unionF;
    final TermFeature intersectF;
    final TermFeature setMinusF;
    final TermFeature infiniteUnionF;
    final TermFeature cardF;
    final TermFeature elementOfF;
    final TermFeature subsetF;
    final TermFeature disjointF;
}
