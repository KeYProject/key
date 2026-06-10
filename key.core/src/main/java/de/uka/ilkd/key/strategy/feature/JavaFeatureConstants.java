/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import org.key_project.prover.strategy.FeatureConstants;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

public class JavaFeatureConstants implements FeatureConstants {
    @Override
    public ProjectionToTerm focusProjection() {
        return null;
    }

    @Override
    public ProjectionToTerm focusProjection(int stepsUpwards) {
        return null;
    }

    @Override
    public ProjectionToTerm focusFormulaProjection() {
        return null;
    }

    @Override
    public Feature matchedAssumesFeature() {
        return null;
    }

    @Override
    public Feature nonDuplicateAppModPositionFeature() {
        return null;
    }

    @Override
    public Feature notInScopeOfModalityFeature() {
        return null;
    }

    @Override
    public Feature diffFindAndIfFeature() {
        return null;
    }

    @Override
    public Feature topLevelFindSucc() {
        return null;
    }

    @Override
    public Feature checkApplyEqFeature() {
        return null;
    }

    @Override
    public Feature findRightishFeature() {
        return null;
    }
}
