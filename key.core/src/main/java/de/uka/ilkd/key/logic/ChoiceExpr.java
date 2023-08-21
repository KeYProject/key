/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.Objects;
import java.util.Set;
import javax.annotation.Nonnull;

/**
 * A ChoiceExpr is a boolean expression that determines whether a taclet or a goal should be
 * activated. {@link ChoiceExpr} are built over and, or, or not. Its atoms are choices
 * ({@code category:option}).
 * <p>
 * This class provides factory methods for constructing an AST.
 *
 * @author Alexander Weigl
 * @version 1 (09.10.22)
 */
public abstract class ChoiceExpr {
    public static final ChoiceExpr TRUE = new True();


    protected ChoiceExpr() {
    }

    public static ChoiceExpr and(ChoiceExpr left, ChoiceExpr right) {
        return new And(left, right);
    }

    public static ChoiceExpr variable(String category, String option) {
        return new Proposition(category, option);
    }

    public static ChoiceExpr or(ChoiceExpr left, ChoiceExpr right) {
        return new Or(left, right);
    }

    public static ChoiceExpr not(ChoiceExpr sub) {
        return new Not(sub);
    }

    /**
     * Evaluate the expression to a boolean value given the current activated choices.
     *
     * @param current activated choices
     * @return true if the expr is true given the assignment in {@code current}
     */
    public abstract boolean eval(@Nonnull Set<Choice> current);

    @Override
    public abstract String toString();

    private static class True extends ChoiceExpr {
        @Override
        public boolean eval(@Nonnull Set<Choice> current) {
            return true;
        }

        @Override
        public String toString() {
            return "true";
        }

    }


    private static class Proposition extends ChoiceExpr {
        public final @Nonnull Choice choice;

        public Proposition(String category, String option) {
            this.choice = new Choice(option, category);
        }

        @Override
        public boolean eval(@Nonnull Set<Choice> current) {
            return current.contains(choice);
        }

        @Override
        public String toString() {
            return choice.name().toString();
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) {
                return true;
            }
            if (!(o instanceof Proposition)) {
                return false;
            }
            Proposition that = (Proposition) o;
            return choice.equals(that.choice);
        }

        @Override
        public int hashCode() {
            return Objects.hash(choice);
        }
    }

    private static class And extends ChoiceExpr {
        public final @Nonnull ChoiceExpr left;
        public final @Nonnull ChoiceExpr right;

        public And(@Nonnull ChoiceExpr left, @Nonnull ChoiceExpr right) {
            this.left = left;
            this.right = right;
        }

        @Override
        public boolean eval(@Nonnull Set<Choice> current) {
            return left.eval(current) && right.eval(current);
        }

        @Override
        public String toString() {
            return "(" + left + " & " + right + ")";
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) {
                return true;
            }
            if (!(o instanceof And)) {
                return false;
            }
            And and = (And) o;
            return left.equals(and.left) && right.equals(and.right);
        }

        @Override
        public int hashCode() {
            return Objects.hash(left, right);
        }
    }

    private static class Or extends ChoiceExpr {
        public final @Nonnull ChoiceExpr left;
        public final @Nonnull ChoiceExpr right;

        public Or(@Nonnull ChoiceExpr left, @Nonnull ChoiceExpr right) {
            this.left = left;
            this.right = right;
        }

        @Override
        public boolean eval(@Nonnull Set<Choice> current) {
            return left.eval(current) || right.eval(current);
        }

        @Override
        public String toString() {
            return "(" + left + " | " + right + ")";
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) {
                return true;
            }
            if (!(o instanceof Or)) {
                return false;
            }
            Or or = (Or) o;
            return left.equals(or.left) && right.equals(or.right);
        }

        @Override
        public int hashCode() {
            return Objects.hash(left, right);
        }
    }

    private static class Not extends ChoiceExpr {
        public final ChoiceExpr sub;

        public Not(ChoiceExpr sub) {
            this.sub = sub;
        }

        @Override
        public boolean eval(@Nonnull Set<Choice> current) {
            return !sub.eval(current);
        }

        @Override
        public String toString() {
            return "!(" + sub + ")";
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) {
                return true;
            }
            if (!(o instanceof Not)) {
                return false;
            }
            Not not = (Not) o;
            return sub.equals(not.sub);
        }

        @Override
        public int hashCode() {
            return Objects.hash(sub);
        }
    }
}
