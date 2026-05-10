package org.key_project.java.ast;

import de.uka.ilkd.key.rule.MatchConditions;
import org.jspecify.annotations.Nullable;
import org.key_project.util.collection.RoList;

import java.util.Objects;

/**
 *
 * @author Alexander Weigl
 * @version 1 (25.04.26)
 */
public class MatchHelper {
    public static @Nullable MatchConditions match(Enum<?> e1, Enum<?> e2, MatchConditions cond) {
        return Objects.equals(e1, e2) ? cond : null;
    }

    public static @Nullable MatchConditions match(int i1, int i2, MatchConditions cond) {
        return i1 == i2 ? cond : null;
    }

    public static @Nullable MatchConditions match(long i1, long i2, MatchConditions cond) {
        return i1 == i2 ? cond : null;
    }

    public static @Nullable MatchConditions match(String s1, String s2, MatchConditions cond) {
        return Objects.equals(s1, s2) ? cond : null;
    }

    public static @Nullable <T extends Matchable> MatchConditions match(RoList<T> seq1, RoList<T> seq2, MatchConditions cond) {
        if (seq1.size() != seq2.size()) {
            return null;
        }
        for (int i = 0; i < seq1.size(); i++) {
            var e1 = seq1.get(i);
            var e2 = seq2.get(i);
            cond = e1.match(e2, cond);
            if (cond == null) {
                return null;
            }
        }
        return cond;
    }

    public static @Nullable MatchConditions match(JavaSourceElement e1, JavaSourceElement e2, MatchConditions cond) {
        return e1.match(e2, cond);
    }

    public static MatchConditions match(boolean b1, boolean b2, MatchConditions cond) {
        return b1 == b2 ? cond : null;
    }
}
