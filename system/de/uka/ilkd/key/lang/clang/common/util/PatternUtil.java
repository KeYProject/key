package de.uka.ilkd.key.lang.clang.common.util;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.logic.op.SchemaVariable;

/**
 * Utilities for program element pattern key creation.
 * 
 * @author oleg.myrk@gmail.com
 */
public class PatternUtil {
        public static class SchemaVariableKey {
        }

        /**
         * A key corresponding to a schema variable.
         */
        public final static SchemaVariableKey SCHEMA_VARIABLE_KEY = new SchemaVariableKey();

        public static class NonExistentKey {
        }

        /**
         * A pattern key that should never have corresponding source key.
         */
        public final static NonExistentKey NON_EXISTENT_KEY = new NonExistentKey();

        /**
         * Builds a pattern key for given program element.
         * @param programElement
         * @return
         */
        public static Object buildKey(IProgramElement programElement) {
                if (programElement instanceof SchemaVariable)
                        return SCHEMA_VARIABLE_KEY;
                else
                        return programElement.getClass();
        }
}
