package de.uka.ilkd.key.lang.clang.common.loader.util;

import java.io.OutputStream;
import java.io.PrintStream;

public class ParenthesesOperator extends cetus.hir.UnaryOperator {
        public static final ParenthesesOperator PARENTHESES = new ParenthesesOperator(0);

        private ParenthesesOperator(int value) {
                super(value);
        }

        /**
         * Used internally -- you may not create arbitrary assignment operators
         * and may only use the ones provided as static members.
         * 
         * @param value
         *                The numeric code of the operator.
         */
        private static String[] names = { "()" };

        /*
         * It is not necessary to override equals or provide cloning, because
         * all possible operators are provided as static objects.
         */

        public void print(OutputStream stream) {
                PrintStream p = new PrintStream(stream);
                p.print(names[value]);
        }

        public String toString() {
                return names[value];
        }

        /**
         * Verifies this operator is valid.
         * 
         * @throws IllegalStateException
         *                 if the operator is invalid.
         */
        public void verify() throws IllegalStateException {
                if (value < 0 || value > 1)
                        throw new IllegalStateException();
        }
}
