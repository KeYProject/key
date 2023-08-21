/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

import java.util.Stack;

import recoder.AbstractService;
import recoder.ModelException;
import recoder.ServiceConfiguration;
import recoder.abstraction.Field;
import recoder.abstraction.PrimitiveType;
import recoder.abstraction.Type;
import recoder.abstraction.Variable;
import recoder.java.Expression;
import recoder.java.JavaProgramFactory;
import recoder.java.ProgramElement;
import recoder.java.expression.Assignment;
import recoder.java.expression.Literal;
import recoder.java.expression.Operator;
import recoder.java.expression.ParenthesizedExpression;
import recoder.java.expression.literal.*;
import recoder.java.expression.operator.*;
import recoder.java.reference.*;

/**
 * Easy constant folder to evaluate Java compile-time constants.
 *
 * @author AL
 */
public class DefaultConstantEvaluator extends AbstractService implements ConstantEvaluator {

    final static BinaryNumericOperation PLUS = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public int eval(int a, int b) {
            return a + b;
        }

        public long eval(long a, long b) {
            return a + b;
        }

        public float eval(float a, float b) {
            return a + b;
        }

        public double eval(double a, double b) {
            return a + b;
        }

        public String eval(String a, String b) {
            if (a == null) {
                fail();
                return null;
            }
            return a + b;
        }
    };
    final static BinaryNumericOperation MINUS = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public int eval(int a, int b) {
            return a - b;
        }

        public long eval(long a, long b) {
            return a - b;
        }

        public float eval(float a, float b) {
            return a - b;
        }

        public double eval(double a, double b) {
            return a - b;
        }

        public String eval(String a, String b) {
            fail();
            return null;
        }
    };
    final static BinaryNumericOperation DIVIDE = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public int eval(int a, int b) {
            return a / b;
        }

        public long eval(long a, long b) {
            return a / b;
        }

        public float eval(float a, float b) {
            return a / b;
        }

        public double eval(double a, double b) {
            return a / b;
        }

        public String eval(String a, String b) {
            fail();
            return null;
        }
        // should catch the div-by-zero exception and re-throw a more
        // meaningful error message
    };
    final static BinaryNumericOperation MODULO = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public int eval(int a, int b) {
            return a % b;
        }

        public long eval(long a, long b) {
            return a % b;
        }

        public float eval(float a, float b) {
            return a % b;
        }

        public double eval(double a, double b) {
            return a % b;
        }

        public String eval(String a, String b) {
            fail();
            return null;
        }
        // should catch the div-by-zero exception and re-throw a more
        // meaningful error message
    };
    final static BinaryNumericOperation TIMES = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public int eval(int a, int b) {
            return a * b;
        }

        public long eval(long a, long b) {
            return a * b;
        }

        public float eval(float a, float b) {
            return a * b;
        }

        public double eval(double a, double b) {
            return a * b;
        }

        public String eval(String a, String b) {
            fail();
            return null;
        }
    };
    final static BinaryNumericOperation SHIFT_LEFT = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public int eval(int a, int b) {
            return a << b;
        }

        public long eval(long a, long b) {
            return a << b;
        }

        public float eval(float a, float b) {
            fail();
            return 0;
        }

        public double eval(double a, double b) {
            fail();
            return 0;
        }

        public String eval(String a, String b) {
            fail();
            return null;
        }
    };
    final static BinaryNumericOperation SHIFT_RIGHT = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public int eval(int a, int b) {
            return a >> b;
        }

        public long eval(long a, long b) {
            return a >> b;
        }

        public float eval(float a, float b) {
            fail();
            return 0;
        }

        public double eval(double a, double b) {
            fail();
            return 0;
        }

        public String eval(String a, String b) {
            fail();
            return null;
        }
    };
    final static BinaryNumericOperation UNSIGNED_SHIFT_RIGHT = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public int eval(int a, int b) {
            return a >>> b;
        }

        public long eval(long a, long b) {
            return a >>> b;
        }

        public float eval(float a, float b) {
            fail();
            return 0;
        }

        public double eval(double a, double b) {
            fail();
            return 0;
        }

        public String eval(String a, String b) {
            fail();
            return null;
        }
    };
    final static BinaryNumericOperation BINARY_AND = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            return a & b;
        }

        public int eval(int a, int b) {
            return a & b;
        }

        public long eval(long a, long b) {
            return a & b;
        }

        public float eval(float a, float b) {
            fail();
            return 0;
        }

        public double eval(double a, double b) {
            fail();
            return 0;
        }

        public String eval(String a, String b) {
            fail();
            return null;
        }
    };
    final static BinaryNumericOperation BINARY_OR = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            return a | b;
        }

        public int eval(int a, int b) {
            return a | b;
        }

        public long eval(long a, long b) {
            return a | b;
        }

        public float eval(float a, float b) {
            fail();
            return 0;
        }

        public double eval(double a, double b) {
            fail();
            return 0;
        }

        public String eval(String a, String b) {
            fail();
            return null;
        }
    };
    final static BinaryNumericOperation BINARY_XOR = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            return a ^ b;
        }

        public int eval(int a, int b) {
            return a ^ b;
        }

        public long eval(long a, long b) {
            return a ^ b;
        }

        public float eval(float a, float b) {
            fail();
            return 0;
        }

        public double eval(double a, double b) {
            fail();
            return 0;
        }

        public String eval(String a, String b) {
            fail();
            return null;
        }
    };
    final static BinaryBooleanOperation EQUALS = new BinaryBooleanOperation() {
        public boolean eval(boolean a, boolean b) {
            return a == b;
        }

        public boolean eval(int a, int b) {
            return a == b;
        }

        public boolean eval(long a, long b) {
            return a == b;
        }

        public boolean eval(float a, float b) {
            return a == b;
        }

        public boolean eval(double a, double b) {
            return a == b;
        }

        public boolean eval(String a, String b) {
            return a == b;
        }
        // the String equals relies on the internalization in EvaluationResult
    };
    final static BinaryBooleanOperation NOT_EQUALS = new BinaryBooleanOperation() {
        public boolean eval(boolean a, boolean b) {
            return a != b;
        }

        public boolean eval(int a, int b) {
            return a != b;
        }

        public boolean eval(long a, long b) {
            return a != b;
        }

        public boolean eval(float a, float b) {
            return a != b;
        }

        public boolean eval(double a, double b) {
            return a != b;
        }

        public boolean eval(String a, String b) {
            return a != b;
        }
    };
    final static BinaryBooleanOperation LESS_THAN = new BinaryBooleanOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public boolean eval(int a, int b) {
            return a < b;
        }

        public boolean eval(long a, long b) {
            return a < b;
        }

        public boolean eval(float a, float b) {
            return a < b;
        }

        public boolean eval(double a, double b) {
            return a < b;
        }

        public boolean eval(String a, String b) {
            fail();
            return false;
        }
    };
    final static BinaryBooleanOperation GREATER_THAN = new BinaryBooleanOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public boolean eval(int a, int b) {
            return a > b;
        }

        public boolean eval(long a, long b) {
            return a > b;
        }

        public boolean eval(float a, float b) {
            return a > b;
        }

        public boolean eval(double a, double b) {
            return a > b;
        }

        public boolean eval(String a, String b) {
            fail();
            return false;
        }
    };
    final static BinaryBooleanOperation LESS_OR_EQUALS = new BinaryBooleanOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public boolean eval(int a, int b) {
            return a <= b;
        }

        public boolean eval(long a, long b) {
            return a <= b;
        }

        public boolean eval(float a, float b) {
            return a <= b;
        }

        public boolean eval(double a, double b) {
            return a <= b;
        }

        public boolean eval(String a, String b) {
            fail();
            return false;
        }
    };
    final static BinaryBooleanOperation GREATER_OR_EQUALS = new BinaryBooleanOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public boolean eval(int a, int b) {
            return a >= b;
        }

        public boolean eval(long a, long b) {
            return a >= b;
        }

        public boolean eval(float a, float b) {
            return a >= b;
        }

        public boolean eval(double a, double b) {
            return a >= b;
        }

        public boolean eval(String a, String b) {
            fail();
            return false;
        }
    };
    final static BinaryBooleanOperation LOGICAL_AND = new BinaryBooleanOperation() {
        public boolean eval(boolean a, boolean b) {
            return a && b;
        }

        public boolean eval(int a, int b) {
            fail();
            return false;
        }

        public boolean eval(long a, long b) {
            fail();
            return false;
        }

        public boolean eval(float a, float b) {
            fail();
            return false;
        }

        public boolean eval(double a, double b) {
            fail();
            return false;
        }

        public boolean eval(String a, String b) {
            fail();
            return false;
        }
    };
    final static BinaryBooleanOperation LOGICAL_OR = new BinaryBooleanOperation() {
        public boolean eval(boolean a, boolean b) {
            return a || b;
        }

        public boolean eval(int a, int b) {
            fail();
            return false;
        }

        public boolean eval(long a, long b) {
            fail();
            return false;
        }

        public boolean eval(float a, float b) {
            fail();
            return false;
        }

        public boolean eval(double a, double b) {
            fail();
            return false;
        }

        public boolean eval(String a, String b) {
            fail();
            return false;
        }
    };
    final static UnaryBooleanOperation LOGICAL_NOT = new UnaryBooleanOperation() {
        public boolean eval(boolean a) {
            return !a;
        }

        public boolean eval(int a) {
            fail();
            return false;
        }

        public boolean eval(long a) {
            fail();
            return false;
        }

        public boolean eval(float a) {
            fail();
            return false;
        }

        public boolean eval(double a) {
            fail();
            return false;
        }

        public boolean eval(String a) {
            fail();
            return false;
        }
    };
    final static UnaryNumericOperation POSITIVE = new UnaryNumericOperation() {
        public boolean eval(boolean a) {
            fail();
            return false;
        }

        public int eval(int a) {
            return +a;
        }

        public long eval(long a) {
            return +a;
        }

        public float eval(float a) {
            return +a;
        }

        public double eval(double a) {
            return +a;
        }

        public String eval(String a) {
            fail();
            return null;
        }
    };
    final static UnaryNumericOperation NEGATIVE = new UnaryNumericOperation() {
        public boolean eval(boolean a) {
            fail();
            return false;
        }

        public int eval(int a) {
            return -a;
        }

        public long eval(long a) {
            return -a;
        }

        public float eval(float a) {
            return -a;
        }

        public double eval(double a) {
            return -a;
        }

        public String eval(String a) {
            fail();
            return null;
        }
    };
    final static UnaryNumericOperation BINARY_NOT = new UnaryNumericOperation() {
        public boolean eval(boolean a) {
            fail();
            return false;
        }

        public int eval(int a) {
            return ~a;
        }

        public long eval(long a) {
            return ~a;
        }

        public float eval(float a) {
            fail();
            return 0;
        }

        public double eval(double a) {
            fail();
            return 0;
        }

        public String eval(String a) {
            fail();
            return null;
        }
    };
    /*
     * Stack holding all variable references that have already been followed. This is used to detect
     * cycles
     */
    private final Stack visitedVariableReferences = new Stack();

    /**
     * Create a new constant evaluator.
     *
     * @param config the configuration this services becomes part of.
     */
    public DefaultConstantEvaluator(ServiceConfiguration config) {
        super(config);
    }

    /**
     * Map primitive type objects to internal integral encoding.
     */
    static int translateType(PrimitiveType t, NameInfo ni) {
        if (t == ni.getIntType()) {
            return INT_TYPE;
        }
        if (t == ni.getBooleanType()) {
            return BOOLEAN_TYPE;
        }
        if (t == ni.getLongType()) {
            return LONG_TYPE;
        }
        if (t == ni.getFloatType()) {
            return FLOAT_TYPE;
        }
        if (t == ni.getDoubleType()) {
            return DOUBLE_TYPE;
        }
        if (t == ni.getByteType()) {
            return BYTE_TYPE;
        }
        if (t == ni.getCharType()) {
            return CHAR_TYPE;
        }
        if (t == ni.getShortType()) {
            return SHORT_TYPE;
        }
        return -1;
    }

    static PrimitiveType translateType(int t, NameInfo ni) {
        switch (t) {
        case INT_TYPE:
            return ni.getIntType();
        case BOOLEAN_TYPE:
            return ni.getBooleanType();
        case LONG_TYPE:
            return ni.getLongType();
        case FLOAT_TYPE:
            return ni.getFloatType();
        case DOUBLE_TYPE:
            return ni.getDoubleType();
        case BYTE_TYPE:
            return ni.getByteType();
        case CHAR_TYPE:
            return ni.getCharType();
        case SHORT_TYPE:
            return ni.getShortType();
        default:
            return null;
        }
    }

    /**
     * Widenes any numerical type short than int (byte, char, short) to at least int.
     */
    static void promoteNumericTypeToInt(ConstantEvaluator.EvaluationResult res) {
        switch (res.getTypeCode()) {
        case BYTE_TYPE:
            res.setInt(res.getByte());
            break;
        case CHAR_TYPE:
            res.setInt(res.getChar());
            break;
        case SHORT_TYPE:
            res.setInt(res.getShort());
            break;
        }
    }

    /**
     * Asumes that both values are widened to at least int type. This is done by
     * {@link #promoteNumericType}. Ensures that both values have equal types, or throws an
     * exception if this is not possible given the set of allowed transformations.
     */
    static void matchTypes(ConstantEvaluator.EvaluationResult lhs,
            ConstantEvaluator.EvaluationResult rhs) {
        switch (lhs.getTypeCode()) {
        case INT_TYPE:
            switch (rhs.getTypeCode()) {
            case LONG_TYPE:
                lhs.setLong(lhs.getInt());
                break;
            case FLOAT_TYPE:
                lhs.setFloat(lhs.getInt());
                break;
            case DOUBLE_TYPE:
                lhs.setDouble(lhs.getInt());
                break;
            }
            break;
        case LONG_TYPE:
            switch (rhs.getTypeCode()) {
            case INT_TYPE:
                rhs.setLong(rhs.getInt());
                break;
            case FLOAT_TYPE:
                lhs.setFloat(lhs.getLong());
                break;
            case DOUBLE_TYPE:
                lhs.setDouble(lhs.getLong());
                break;
            }
            break;
        case FLOAT_TYPE:
            switch (rhs.getTypeCode()) {
            case INT_TYPE:
                rhs.setFloat(rhs.getInt());
                break;
            case LONG_TYPE:
                rhs.setFloat(rhs.getLong());
                break;
            case DOUBLE_TYPE:
                lhs.setDouble(lhs.getFloat());
                break;
            }
            break;
        case DOUBLE_TYPE:
            switch (rhs.getTypeCode()) {
            case INT_TYPE:
                rhs.setDouble(rhs.getInt());
                break;
            case LONG_TYPE:
                rhs.setDouble(rhs.getLong());
                break;
            case FLOAT_TYPE:
                rhs.setDouble(rhs.getFloat());
                break;
            }
            break;
        case STRING_TYPE:
            switch (rhs.getTypeCode()) {
            case INT_TYPE:
                rhs.setString(String.valueOf(rhs.getInt()));
                break;
            case LONG_TYPE:
                rhs.setString(String.valueOf(rhs.getLong()));
                break;
            case FLOAT_TYPE:
                rhs.setString(String.valueOf(rhs.getFloat()));
                break;
            case DOUBLE_TYPE:
                rhs.setString(String.valueOf(rhs.getDouble()));
                break;
            }
            break;
        }
        // if the rules above did not produce equal types,
        // something is wrong, e.g. boolean + non-boolean,
        // non-String + String
        if (lhs.getTypeCode() != rhs.getTypeCode()) {
            throw new RuntimeException(
                "Operand types are illegal: " + lhs.getTypeCode() + " / " + rhs.getTypeCode());
        }
    }

    /**
     * Obeyes the automatic narrowing rules for int-constants. If a combination of int and
     * short/char/byte is found, and the value of the int constant fits into the range of the
     * smaller type, the int constant is narrowed.
     */
    static void matchAssignmentTypes(ConstantEvaluator.EvaluationResult lhs,
            ConstantEvaluator.EvaluationResult rhs) {
        int value;
        switch (lhs.getTypeCode()) {
        case INT_TYPE:
            switch (rhs.getTypeCode()) {
            case BYTE_TYPE:
                value = lhs.getInt();
                if (Byte.MIN_VALUE <= value && value <= Byte.MAX_VALUE) {
                    lhs.setByte((byte) value);
                } else {
                    rhs.setInt(rhs.getByte());
                }
                return;
            case CHAR_TYPE:
                value = lhs.getInt();
                if (Character.MIN_VALUE <= value && value <= Character.MAX_VALUE) {
                    lhs.setChar((char) value);
                } else {
                    rhs.setInt(rhs.getChar());
                }
                return;
            case SHORT_TYPE:
                value = lhs.getInt();
                if (Short.MIN_VALUE <= value && value <= Short.MAX_VALUE) {
                    lhs.setShort((short) value);
                } else {
                    rhs.setInt(rhs.getShort());
                }
                return;
            }
            break;
        case BYTE_TYPE:
            if (rhs.getTypeCode() == INT_TYPE) {
                value = rhs.getInt();
                if (Byte.MIN_VALUE <= value && value <= Byte.MAX_VALUE) {
                    rhs.setByte((byte) value);
                } else {
                    lhs.setInt(lhs.getByte());
                }
                return;
            }
            break;
        case SHORT_TYPE:
            if (rhs.getTypeCode() == INT_TYPE) {
                value = rhs.getInt();
                if (Short.MIN_VALUE <= value && value <= Short.MAX_VALUE) {
                    rhs.setShort((short) value);
                } else {
                    lhs.setInt(lhs.getShort());
                }
                return;
            }
            break;
        case CHAR_TYPE:
            if (rhs.getTypeCode() == INT_TYPE) {
                value = rhs.getInt();
                if (Character.MIN_VALUE <= value && value <= Character.MAX_VALUE) {
                    rhs.setChar((char) value);
                } else {
                    lhs.setInt(lhs.getChar());
                }
                return;
            }
            break;
        }
        matchTypes(lhs, rhs);
    }

    /**
     * Obeyes a special rule for the conditional operator: byte - short - combinations are resolved
     * to short types. Promote combinations byte - char, short - char (implicit narrowing is defined
     * for int types only).
     */
    static void matchConditionalTypes(ConstantEvaluator.EvaluationResult lhs,
            ConstantEvaluator.EvaluationResult rhs) {
        switch (lhs.getTypeCode()) {
        case BYTE_TYPE:
            switch (rhs.getTypeCode()) {
            case SHORT_TYPE: // byte x short -> short x short
                lhs.setShort(lhs.getByte());
                return;
            case CHAR_TYPE: // byte x char -> int x int
                promoteNumericTypeToInt(lhs);
                promoteNumericTypeToInt(rhs);
                return;
            }
            break;
        case CHAR_TYPE:
            switch (rhs.getTypeCode()) {
            case BYTE_TYPE: // char x byte, char x short -> int x int
            case SHORT_TYPE:
                promoteNumericTypeToInt(lhs);
                promoteNumericTypeToInt(rhs);
                return;
            }
            break;
        case SHORT_TYPE:
            switch (rhs.getTypeCode()) {
            case BYTE_TYPE: // short x byte -> short x short
                rhs.setShort(rhs.getByte());
                return;
            case CHAR_TYPE: // short x char -> int x int
                promoteNumericTypeToInt(lhs);
                promoteNumericTypeToInt(rhs);
                return;
            }
            break;
        }
        matchAssignmentTypes(lhs, rhs);
    }

    static String parseJavaString(String text) {
        int len = text.length();
        StringBuilder buf = new StringBuilder(len);
        for (int i = 1; i < len - 1; i += 1) {
            char c = text.charAt(i);
            if (c != '\\') {
                buf.append(c);
            } else {
                i += 1;
                switch (text.charAt(i)) {
                case 'b':
                    buf.append('\b');
                    break;
                case 't':
                    buf.append('\t');
                    break;
                case 'n':
                    buf.append('\n');
                    break;
                case 'f':
                    buf.append('\f');
                    break;
                case 'r':
                    buf.append('\r');
                    break;
                case '\"':
                    buf.append('\"');
                    break;
                case '\'':
                    buf.append('\'');
                    break;
                case '\\':
                    buf.append('\\');
                    break;
                case 'u':
                    // skip an arbitrary number of u's
                    i += 1;
                    while (text.charAt(i) == 'u') {
                        i += 1;
                    }
                    // the following must be a 4-digit hex value
                    buf.append((char) Integer.parseInt(text.substring(i, i + 4), 16));
                    i += 4;
                    break;
                case '0':
                case '1':
                case '2':
                case '3':
                case '4':
                case '5':
                case '6':
                case '7':
                    int j = i + 1;
                    while (j < len && text.charAt(j) >= '0' && text.charAt(j) <= '7') {
                        j += 1;
                    }
                    buf.append((char) Integer.parseInt(text.substring(i, j), 8));
                    i = j;
                    break;
                default:
                    throw new ModelException("Bad character representation: " + text);
                }
            }
        }
        return buf.toString();
    }

    static void doPrimitiveTypeCast(int newType, ConstantEvaluator.EvaluationResult res) {
        int oldType = res.getTypeCode();
        if (oldType == newType) {
            return;
        }
        if (oldType == BOOLEAN_TYPE || newType == BOOLEAN_TYPE) {
            throw new ModelException("Cast not allowed");
        }
        switch (oldType) {
        case BYTE_TYPE:
            switch (newType) {
            case SHORT_TYPE:
                res.setShort(res.getByte());
                return;
            case CHAR_TYPE:
                res.setChar((char) res.getByte());
                return;
            case INT_TYPE:
                res.setInt(res.getByte());
                return;
            case LONG_TYPE:
                res.setLong(res.getByte());
                return;
            case FLOAT_TYPE:
                res.setFloat(res.getByte());
                return;
            case DOUBLE_TYPE:
                res.setDouble(res.getByte());
                return;
            }
            break;
        case SHORT_TYPE:
            switch (newType) {
            case BYTE_TYPE:
                res.setByte((byte) res.getShort());
                return;
            case CHAR_TYPE:
                res.setChar((char) res.getShort());
                return;
            case INT_TYPE:
                res.setInt(res.getShort());
                return;
            case LONG_TYPE:
                res.setLong(res.getShort());
                return;
            case FLOAT_TYPE:
                res.setFloat(res.getShort());
                return;
            case DOUBLE_TYPE:
                res.setDouble(res.getShort());
                return;
            }
            break;
        case CHAR_TYPE:
            switch (newType) {
            case BYTE_TYPE:
                res.setByte((byte) res.getChar());
                return;
            case SHORT_TYPE:
                res.setShort((short) res.getChar());
                return;
            case INT_TYPE:
                res.setInt(res.getChar());
                return;
            case LONG_TYPE:
                res.setLong(res.getChar());
                return;
            case FLOAT_TYPE:
                res.setFloat(res.getChar());
                return;
            case DOUBLE_TYPE:
                res.setDouble(res.getChar());
                return;
            }
            break;
        case INT_TYPE:
            switch (newType) {
            case BYTE_TYPE:
                res.setByte((byte) res.getInt());
                return;
            case SHORT_TYPE:
                res.setShort((short) res.getInt());
                return;
            case CHAR_TYPE:
                res.setChar((char) res.getInt());
                return;
            case LONG_TYPE:
                res.setLong(res.getInt());
                return;
            case FLOAT_TYPE:
                res.setFloat((float) res.getInt());
                return;
            case DOUBLE_TYPE:
                res.setDouble(res.getInt());
                return;
            }
            break;
        case LONG_TYPE:
            switch (newType) {
            case BYTE_TYPE:
                res.setByte((byte) res.getLong());
                return;
            case SHORT_TYPE:
                res.setShort((short) res.getLong());
                return;
            case CHAR_TYPE:
                res.setChar((char) res.getLong());
                return;
            case INT_TYPE:
                res.setInt((int) res.getLong());
                return;
            case FLOAT_TYPE:
                res.setFloat((float) res.getLong());
                return;
            case DOUBLE_TYPE:
                res.setDouble((double) res.getLong());
                return;
            }
            break;
        case FLOAT_TYPE:
            switch (newType) {
            case BYTE_TYPE:
                res.setByte((byte) res.getFloat());
                return;
            case SHORT_TYPE:
                res.setShort((short) res.getFloat());
                return;
            case CHAR_TYPE:
                res.setChar((char) res.getFloat());
                return;
            case INT_TYPE:
                res.setInt((int) res.getFloat());
                return;
            case LONG_TYPE:
                res.setLong((long) res.getFloat());
                return;
            case DOUBLE_TYPE:
                res.setDouble(res.getFloat());
                return;
            }
            break;
        case DOUBLE_TYPE:
            switch (newType) {
            case BYTE_TYPE:
                res.setByte((byte) res.getDouble());
                return;
            case SHORT_TYPE:
                res.setShort((short) res.getDouble());
                return;
            case CHAR_TYPE:
                res.setChar((char) res.getDouble());
                return;
            case INT_TYPE:
                res.setInt((int) res.getDouble());
                return;
            case LONG_TYPE:
                res.setLong((long) res.getDouble());
                return;
            case FLOAT_TYPE:
                res.setFloat((float) res.getDouble());
                return;
            }
            break;
        }
    }

    NameInfo getNameInfo() {
        return serviceConfiguration.getNameInfo();
    }

    SourceInfo getSourceInfo() {
        return serviceConfiguration.getSourceInfo();
    }

    /**
     * Returns the type of a constant expression if it is a compile-time constant as defined in the
     * Java language specification, or <CODE>null
     * </CODE> if it is not.
     *
     * @param expr the expression to evaluate.
     * @return the type of the expression, or <CODE>null</CODE> if the expression is not constant.
     */
    public Type getCompileTimeConstantType(Expression expr) {
        ConstantEvaluator.EvaluationResult res = new ConstantEvaluator.EvaluationResult();
        if (!isCompileTimeConstant(expr, res)) {
            return null;
        }
        return res.getPrimitiveType(getNameInfo());
    }

    /**
     * Checks if the given expression is a compile-time constant as defined in the Java language
     * specification.
     *
     * @param expr the expression to evaluate.
     * @return <CODE>true</CODE>, if the expression is a compile-time constant, <CODE>false</CODE>
     *         otherwise.
     */
    public boolean isCompileTimeConstant(Expression expr) {
        return isCompileTimeConstant(expr, new ConstantEvaluator.EvaluationResult());
    }

    /**
     * Checks if the given expression is a compile-time constant as defined in the Java language
     * specification, and derives the result.
     *
     * @param expr the expression to evaluate.
     * @param res the result of the evaluation; contains the type encoding and the result value.
     * @return <CODE>true</CODE>, if the expression is a compile-time constant, <CODE>false</CODE>
     *         otherwise.
     */
    public boolean isCompileTimeConstant(Expression expr, ConstantEvaluator.EvaluationResult res) {
        if (expr instanceof Literal) {
            if (expr instanceof IntLiteral) {
                String v = ((IntLiteral) expr).getValue();
                res.setInt(JavaProgramFactory.parseInt(v));
                return true;
            } else if (expr instanceof StringLiteral) {
                res.setString(parseJavaString(((StringLiteral) expr).getValue()));
                return true;
            } else if (expr instanceof BooleanLiteral) {
                res.setBoolean(((BooleanLiteral) expr).getValue());
                return true;
            } else if (expr instanceof NullLiteral) {
                // we may interpret that as a String, here.
                res.setString(null);
                return true;
            } else if (expr instanceof CharLiteral) {
                res.setChar(parseJavaString(((CharLiteral) expr).getValue()).charAt(0));
                return true;
            } else if (expr instanceof LongLiteral) {
                String v = ((LongLiteral) expr).getValue();
                res.setLong(JavaProgramFactory.parseLong(v));
                return true;
            } else if (expr instanceof FloatLiteral) {
                String v = ((FloatLiteral) expr).getValue();
                res.setFloat(Float.valueOf(v));
                return true;
            } else if (expr instanceof DoubleLiteral) {
                String v = ((DoubleLiteral) expr).getValue();
                res.setDouble(Double.valueOf(v));
                return true;
            }
            throw new ModelException("Unknown literal type");
        }
        if (expr instanceof Operator) {
            if (expr instanceof Assignment) {
                // Assignments are not considered compile-time constants (!)
                return false;
            }

            Operator op = (Operator) expr;
            if (op instanceof TypeOperator) {
                if (op instanceof TypeCast) {
                    if (!isCompileTimeConstant(((TypeCast) expr).getExpressionAt(0), res)) {
                        return false;
                    }
                    int newType = -1;
                    Type to = getSourceInfo().getType(((TypeCast) expr).getTypeReference());
                    if (to instanceof PrimitiveType) {
                        newType = translateType((PrimitiveType) to, getNameInfo());
                    } else if (to == getNameInfo().getJavaLangString()) {
                        newType = STRING_TYPE;
                        // reject casts from anything else than Strings.
                        // note that we considered nulls as Strings.
                        return res.getTypeCode() == STRING_TYPE;
                    } else {
                        // other non-primitive types are not seen as constants
                        return false;
                    }
                    doPrimitiveTypeCast(newType, res);
                    return true;
                }
                // Instanceof, New, NewArray are not considered constants
                return false;
            }

            if (op instanceof ParenthesizedExpression) {
                return isCompileTimeConstant(op.getExpressionAt(0), res);
            }

            // normalize: widen numerical types shorter than int
            // this is also necessary for unary operations (e.g. unary plus!)
            // except parentheses
            promoteNumericTypeToInt(res);

            ConstantEvaluator.EvaluationResult lhs = null;
            ConstantEvaluator.EvaluationResult rhs = null;

            // find out, which operator is meant
            UnaryNumericOperation uno = null;
            UnaryBooleanOperation ubo = null;
            BinaryNumericOperation bno = null;
            BinaryBooleanOperation bbo = null;

            switch (op.getArity()) {
            case 1: // unary operations

                if (!isCompileTimeConstant(op.getExpressionAt(0), res)) {
                    return false;
                }

                if (op instanceof Positive) {
                    uno = POSITIVE;
                } else if (op instanceof Negative) {
                    uno = NEGATIVE;
                } else if (op instanceof BinaryNot) {
                    uno = BINARY_NOT;
                } else if (op instanceof LogicalNot) {
                    ubo = LOGICAL_NOT;
                }
                break;
            case 2: // binary operations
                if (!isCompileTimeConstant(op.getExpressionAt(0), res)) {
                    return false;
                }
                // widen type
                lhs = res;
                promoteNumericTypeToInt(lhs);
                /*
                 * The allocation could be optimized away if the contents of the res/lhs object
                 * would be stored locally and res would be reused for the rhs call. However,
                 * performance is not critical here.
                 */
                rhs = new ConstantEvaluator.EvaluationResult();
                // evaluate right-hand side; finish if not constant
                if (!isCompileTimeConstant(op.getExpressionAt(1), rhs)) {
                    return false;
                }
                // widen numerical types shorter than int
                promoteNumericTypeToInt(rhs);

                // widen the remaining types to match both argument types
                matchTypes(lhs, rhs);

                if (op instanceof ComparativeOperator) {
                    if (op instanceof Equals) {
                        bbo = EQUALS;
                    } else if (op instanceof NotEquals) {
                        bbo = NOT_EQUALS;
                    } else if (op instanceof GreaterThan) {
                        bbo = GREATER_THAN;
                    } else if (op instanceof LessThan) {
                        bbo = LESS_THAN;
                    } else if (op instanceof GreaterOrEquals) {
                        bbo = GREATER_OR_EQUALS;
                    } else if (op instanceof LessOrEquals) {
                        bbo = LESS_OR_EQUALS;
                    } else if (op instanceof LogicalAnd) {
                        bbo = LOGICAL_AND;
                    } else if (op instanceof LogicalOr) {
                        bbo = LOGICAL_OR;
                    }
                } else if (op instanceof Plus) {
                    bno = PLUS;
                } else if (op instanceof Minus) {
                    bno = MINUS;
                } else if (op instanceof Times) {
                    bno = TIMES;
                } else if (op instanceof Divide) {
                    bno = DIVIDE;
                } else if (op instanceof Modulo) {
                    bno = MODULO;
                } else if (op instanceof ShiftLeft) {
                    bno = SHIFT_LEFT;
                } else if (op instanceof ShiftRight) {
                    bno = SHIFT_RIGHT;
                } else if (op instanceof UnsignedShiftRight) {
                    bno = UNSIGNED_SHIFT_RIGHT;
                } else if (op instanceof BinaryAnd) {
                    bno = BINARY_AND;
                } else if (op instanceof BinaryOr) {
                    bno = BINARY_OR;
                } else if (op instanceof BinaryXOr) {
                    bno = BINARY_XOR;
                } else if (op instanceof LogicalAnd) {
                    bbo = LOGICAL_AND;
                } else if (op instanceof LogicalOr) {
                    bbo = LOGICAL_OR;
                }
                break;
            case 3:
                // this must be the conditional (?:)
                if (!isCompileTimeConstant(op.getExpressionAt(0), res)) {
                    return false;
                }
                if (res.getTypeCode() != BOOLEAN_TYPE) {
                    throw new ModelException("No boolean expression in ?:");
                }
                boolean cond = res.getBoolean();
                // evaluate both sides; finish if not constant

                lhs = res; // overwrite old values
                if (!isCompileTimeConstant(op.getExpressionAt(1), lhs)) {
                    return false;
                }
                rhs = new ConstantEvaluator.EvaluationResult();
                if (!isCompileTimeConstant(op.getExpressionAt(2), rhs)) {
                    return false;
                }
                matchConditionalTypes(lhs, rhs);

                switch (lhs.getTypeCode()) { // matches type of rhs
                case BOOLEAN_TYPE:
                    res.setBoolean(cond ? lhs.getBoolean() : rhs.getBoolean());
                    break;
                case BYTE_TYPE:
                    res.setByte(cond ? lhs.getByte() : rhs.getByte());
                    break;
                case SHORT_TYPE:
                    res.setShort(cond ? lhs.getShort() : rhs.getShort());
                    break;
                case CHAR_TYPE:
                    res.setChar(cond ? lhs.getChar() : rhs.getChar());
                    break;
                case INT_TYPE:
                    res.setInt(cond ? lhs.getInt() : rhs.getInt());
                    break;
                case LONG_TYPE:
                    res.setLong(cond ? lhs.getLong() : rhs.getLong());
                    break;
                case FLOAT_TYPE:
                    res.setFloat(cond ? lhs.getFloat() : rhs.getFloat());
                    break;
                case DOUBLE_TYPE:
                    res.setDouble(cond ? lhs.getDouble() : rhs.getDouble());
                    break;
                case STRING_TYPE:
                    res.setString(cond ? lhs.getString() : rhs.getString());
                    break;
                }
                return true;
            }

            if (bno != null) {
                switch (lhs.getTypeCode()) {
                case BOOLEAN_TYPE:
                    lhs.setBoolean(bno.eval(lhs.getBoolean(), rhs.getBoolean()));
                    break;
                case INT_TYPE:
                    lhs.setInt(bno.eval(lhs.getInt(), rhs.getInt()));
                    break;
                case LONG_TYPE:
                    lhs.setLong(bno.eval(lhs.getLong(), rhs.getLong()));
                    break;
                case FLOAT_TYPE:
                    lhs.setFloat(bno.eval(lhs.getFloat(), rhs.getFloat()));
                    break;
                case DOUBLE_TYPE:
                    lhs.setDouble(bno.eval(lhs.getDouble(), rhs.getDouble()));
                    break;
                case STRING_TYPE:
                    lhs.setString(bno.eval(lhs.getString(), rhs.getString()));
                    break;
                }
                return true;
            }

            if (bbo != null) {
                switch (lhs.getTypeCode()) {
                case BOOLEAN_TYPE:
                    lhs.setBoolean(bbo.eval(lhs.getBoolean(), rhs.getBoolean()));
                    break;
                case INT_TYPE:
                    lhs.setBoolean(bbo.eval(lhs.getInt(), rhs.getInt()));
                    break;
                case LONG_TYPE:
                    lhs.setBoolean(bbo.eval(lhs.getLong(), rhs.getLong()));
                    break;
                case FLOAT_TYPE:
                    lhs.setBoolean(bbo.eval(lhs.getFloat(), rhs.getFloat()));
                    break;
                case DOUBLE_TYPE:
                    lhs.setBoolean(bbo.eval(lhs.getDouble(), rhs.getDouble()));
                    break;
                case STRING_TYPE:
                    lhs.setBoolean(bbo.eval(lhs.getString(), rhs.getString()));
                    break;
                }
                return true;
            }

            if (uno != null) {
                switch (res.getTypeCode()) {
                case BOOLEAN_TYPE:
                    res.setBoolean(uno.eval(res.getBoolean()));
                    break;
                case INT_TYPE:
                    res.setInt(uno.eval(res.getInt()));
                    break;
                case LONG_TYPE:
                    res.setLong(uno.eval(res.getLong()));
                    break;
                case FLOAT_TYPE:
                    res.setFloat(uno.eval(res.getFloat()));
                    break;
                case DOUBLE_TYPE:
                    res.setDouble(uno.eval(res.getDouble()));
                    break;
                case STRING_TYPE:
                    res.setString(uno.eval(res.getString()));
                    break;
                }
                return true;
            }

            if (ubo != null) {
                switch (res.getTypeCode()) {
                case BOOLEAN_TYPE:
                    res.setBoolean(ubo.eval(res.getBoolean()));
                    break;
                case INT_TYPE:
                    res.setBoolean(ubo.eval(res.getInt()));
                    break;
                case LONG_TYPE:
                    res.setBoolean(ubo.eval(res.getLong()));
                    break;
                case FLOAT_TYPE:
                    res.setBoolean(ubo.eval(res.getFloat()));
                    break;
                case DOUBLE_TYPE:
                    res.setBoolean(ubo.eval(res.getDouble()));
                    break;
                case STRING_TYPE:
                    res.setBoolean(ubo.eval(res.getString()));
                    break;
                }
                return true;
            }

            throw new ModelException("Unknown operator " + op.getClass().getName() + "?!");

        }
        if (expr instanceof UncollatedReferenceQualifier) {
            ProgramElement pe = getSourceInfo().resolveURQ((UncollatedReferenceQualifier) expr);
            if (pe instanceof VariableReference) {
                expr = (VariableReference) pe;
            } else {
                return false;
            }
        }
        if (expr instanceof VariableReference) {
            // check if it has an access path consisting of names only
            if (expr instanceof FieldReference) {
                ReferencePrefix pre = ((FieldReference) expr).getReferencePrefix();
                while (pre != null) {
                    if (pre instanceof FieldReference || pre instanceof PackageReference
                            || pre instanceof TypeReference
                            || pre instanceof UncollatedReferenceQualifier) {
                        pre = ((ReferenceSuffix) pre).getReferencePrefix();
                    } else {
                        // ArrayReference, MethodReference, New, ...
                        return false; // not considered constant
                    }
                }
            }
            Variable v = getSourceInfo().getVariable((VariableReference) expr);
            // unknown vars are not our problem
            // constants must be final (and static if they are fields)
            if (v == null || !v.isFinal() || (v instanceof Field && !((Field) v).isStatic())) {
                return false;
            }
            // get type of constant - we are not interested in all types.
            int vtype = -1;
            Type vt = v.getType();
            if (vt instanceof PrimitiveType) {
                vtype = translateType((PrimitiveType) vt, getNameInfo());
            } else if (vt == getNameInfo().getJavaLangString()) {
                vtype = STRING_TYPE;
            }
            if (vtype == -1) {
                return false;
            }
            if (visitedVariableReferences.contains(expr)) {
                return false;
            }
            visitedVariableReferences.push(expr);
            try {
                ProgramModelInfo qs = v.getProgramModelInfo();
                if (qs instanceof SourceInfo) {
                    SourceInfo ais = (SourceInfo) qs;
                    expr = ais.getVariableSpecification(v).getInitializer();
                    if (expr == null) {
                        return false;
                    }
                    if (!isCompileTimeConstant(expr, res)) {
                        return false;
                    }
                    // cast to type of constant variable
                    doPrimitiveTypeCast(vtype, res);
                    return true;
                } else if (qs instanceof ByteCodeInfo) {
                    ByteCodeInfo bis = (ByteCodeInfo) qs;
                    String val = bis.getFieldInfo((Field) v).getConstantValue();
                    if (val == null) {
                        return false;
                    }
                    switch (vtype) {
                    case BOOLEAN_TYPE:
                        res.setBoolean(Integer.parseInt(val) != 0);
                        break;
                    case BYTE_TYPE:
                        res.setByte((byte) Integer.parseInt(val));
                        break;
                    case SHORT_TYPE:
                        res.setShort((short) Integer.parseInt(val));
                        break;
                    case CHAR_TYPE:
                        res.setChar((char) Integer.parseInt(val));
                        break;
                    case INT_TYPE:
                        res.setInt(Integer.parseInt(val));
                        break;
                    case LONG_TYPE:
                        res.setLong(Long.parseLong(val));
                        break;
                    case FLOAT_TYPE:
                        if (val.equals("NaN")) {
                            // may occur in byte code?!
                            res.setFloat(Float.NaN);
                        } else {
                            res.setFloat(Float.valueOf(val));
                        }
                        break;
                    case DOUBLE_TYPE:
                        if (val.equals("NaN")) {
                            // may occur in byte code?!
                            res.setDouble(Double.NaN);
                        } else {
                            res.setDouble(Double.valueOf(val));
                        }
                        break;
                    case STRING_TYPE:
                        res.setString(val);
                        break;
                    }
                    return true;
                }
            } finally {
                visitedVariableReferences.pop();
            }
            return false;
        }
        // all other kinds of expressions are not considered constant
        return false;
    }

    static abstract class Operation {
        protected void fail() {
            throw new ModelException("Operand types are illegal");
        }
    }

    static abstract class BinaryNumericOperation extends Operation {
        public abstract boolean eval(boolean a, boolean b);

        public abstract int eval(int a, int b);

        public abstract long eval(long a, long b);

        public abstract float eval(float a, float b);

        public abstract double eval(double a, double b);

        public abstract String eval(String a, String b);
    }

    static abstract class BinaryBooleanOperation extends Operation {
        public abstract boolean eval(boolean a, boolean b);

        public abstract boolean eval(int a, int b);

        public abstract boolean eval(long a, long b);

        public abstract boolean eval(float a, float b);

        public abstract boolean eval(double a, double b);

        public abstract boolean eval(String a, String b);
    }

    static abstract class UnaryNumericOperation extends Operation {
        public abstract boolean eval(boolean a);

        public abstract int eval(int a);

        public abstract long eval(long a);

        public abstract float eval(float a);

        public abstract double eval(double a);

        public abstract String eval(String a);
    }

    static abstract class UnaryBooleanOperation extends Operation {
        public abstract boolean eval(boolean a);

        public abstract boolean eval(int a);

        public abstract boolean eval(long a);

        public abstract boolean eval(float a);

        public abstract boolean eval(double a);

        public abstract boolean eval(String a);
    }
}
