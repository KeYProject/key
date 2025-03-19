/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

public class IncompatibleArrayElementSort extends BinaryFeature {

    private final ProjectionToTerm row;
    private final ProjectionToTerm matrix;

    public IncompatibleArrayElementSort(ProjectionToTerm row, ProjectionToTerm matrix) {
        this.matrix = matrix;
        this.row = row;
    }

    public static IncompatibleArrayElementSort create(ProjectionToTerm row,
            ProjectionToTerm matrix) {
        return new IncompatibleArrayElementSort(row, matrix);
    }

    @Override
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        Term t_row = row.toTerm(app, pos, goal);
        Term t_matrix = matrix.toTerm(app, pos, goal);

        if (!(t_matrix.sort() instanceof ArraySort)) {
            return false;
        }

        final Sort matrixElementSort = ((ArraySort) t_matrix.sort()).elementSort();
        final Sort rowSort = t_row.sort();

        if (rowSort.extendsTrans(matrixElementSort)) {
            return false;
        }

        JavaInfo javaInfo = goal.proof().getServices().getJavaInfo();
        TypeConverter tc = goal.proof().getServices().getTypeConverter();

        KeYJavaType rowKJT = javaInfo.getKeYJavaType(rowSort);
        if (rowKJT == null || rowKJT.getJavaType() == null) {
            return false;
        }
        KeYJavaType matrixElementKJT = javaInfo.getKeYJavaType(matrixElementSort);
        if (matrixElementKJT == null || matrixElementKJT.getJavaType() == null) {
            return false;
        }

        return !tc.isAssignableTo(rowKJT, matrixElementKJT);
    }
}
