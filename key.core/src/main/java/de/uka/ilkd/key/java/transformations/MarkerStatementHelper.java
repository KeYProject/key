/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.transformations;

import com.github.javaparser.ast.DataKey;
import com.github.javaparser.ast.jml.stmt.JmlExpressionStmt;
import com.github.javaparser.ast.key.KeyMergePointStmt;

/**
 * Helper class for marking {@code assert}/{@code assume}/{@code set} statements and merge points
 * in the JMLtk AST during the JML transformation.
 * <p>
 * The transformation ({@code JMLTransformer}) self-marks the respective nodes with these data
 * keys; the KeY loader ({@code JP2KeYConverter}) later reads them to create the corresponding
 * KeY AST statements.
 *
 * @author Alexander Weigl
 * @version 1 (3/4/26)
 */
public class MarkerStatementHelper {
    public static final int KIND_UNKNOWN = 0;
    public static final int KIND_ASSERT = 1;
    public static final int KIND_ASSUME = 2;
    public static final int KIND_SET = 3;
    public static final int KIND_MERGE_POINT = 4;

    /**
     * Marks a {@link JmlExpressionStmt} that represents an {@code assert} or {@code assume}
     * statement.
     */
    public static final DataKey<JmlExpressionStmt> KEY_ASSIGN = new DataKey<>() {
    };

    /**
     * Marks a {@link JmlExpressionStmt} that represents a {@code set} statement (a KeY-specific
     * assignment).
     */
    public static final DataKey<JmlExpressionStmt> KEY_ASSERT = new DataKey<>() {
    };

    /**
     * Marks a {@link KeyMergePointStmt} as the KeY-specific merge point statement.
     */
    public static final DataKey<KeyMergePointStmt> KEY_MERGE_POINT = new DataKey<>() {
    };
}
