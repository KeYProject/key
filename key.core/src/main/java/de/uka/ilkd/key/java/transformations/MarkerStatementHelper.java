package de.uka.ilkd.key.java.transformations;

import com.github.javaparser.ast.DataKey;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLMergePointDecl;
import de.uka.ilkd.key.speclang.njml.JmlParser;

/**
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

    public static final DataKey<KeyAst.Expression> KEY_EXPR = new DataKey<>(){};
    public static final DataKey<KeyAst.SetStatementContext> KEY_ASSIGN = new DataKey<>(){};
    public static final DataKey<TextualJMLMergePointDecl> KEY_MERGE_POINT = new DataKey<>(){};
}
