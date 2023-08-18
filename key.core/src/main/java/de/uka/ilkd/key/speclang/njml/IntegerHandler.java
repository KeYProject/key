/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.util.EnumMap;
import java.util.IdentityHashMap;
import java.util.Map;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator;

import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.*;

public class IntegerHandler extends LDTHandler {
    private final Map<JMLOperator, TypedOperator> jmlCheckedIntMap =
        new EnumMap<>(JMLOperator.class);
    private final Map<JMLOperator, TypedOperator> jmlCheckedLongMap =
        new EnumMap<>(JMLOperator.class);
    private final Map<JMLOperator, TypedOperator> jmlBigintMap = new EnumMap<>(JMLOperator.class);
    private final Map<Type, Map<JMLOperator, TypedOperator>> opCategories = new IdentityHashMap<>();

    /**
     * The spec math mode to use for all following calls to build.
     */
    private SpecMathMode specMathMode;

    public IntegerHandler(Services services, SpecMathMode specMathMode) {
        super(services);

        if (specMathMode == null) {
            throw new IllegalArgumentException("specMathMode cannot be null");
        }

        this.specMathMode = specMathMode;

        var intKjt = services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT);
        var longKjt = services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_LONG);
        var bigIntKjt = services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BIGINT);

        var intLDT = services.getTypeConverter().getIntegerLDT();
        Map<JMLOperator, TypedOperator> jmlIntMap = new EnumMap<>(JMLOperator.class);
        jmlIntMap.put(ADD, new TypedOperator(intKjt, intLDT.getAddJint()));
        jmlIntMap.put(SUBTRACT, new TypedOperator(intKjt, intLDT.getSubJint()));
        jmlIntMap.put(MULT, new TypedOperator(intKjt, intLDT.getMulJint()));
        jmlIntMap.put(DIVISION, new TypedOperator(intKjt, intLDT.getDivJint()));
        jmlIntMap.put(MODULO, new TypedOperator(intKjt, intLDT.getModJint()));
        jmlIntMap.put(BITWISE_AND, new TypedOperator(intKjt, intLDT.getBitwiseAndJInt()));
        jmlIntMap.put(BITWISE_OR, new TypedOperator(intKjt, intLDT.getBitwiseOrJInt()));
        jmlIntMap.put(BITWISE_XOR, new TypedOperator(intKjt, intLDT.getXorJint()));
        jmlIntMap.put(SHIFT_RIGHT, new TypedOperator(intKjt, intLDT.getShiftrightJint()));
        jmlIntMap.put(SHIFT_LEFT, new TypedOperator(intKjt, intLDT.getShiftleftJint()));
        jmlIntMap.put(UNSIGNED_SHIFT_RIGHT,
            new TypedOperator(intKjt, intLDT.getUnsignedshiftrightJint()));
        jmlIntMap.put(BITWISE_NEGATE, new TypedOperator(intKjt, intLDT.getBitwiseNegateJint()));
        jmlIntMap.put(UNARY_MINUS, new TypedOperator(intKjt, intLDT.getUnaryMinusJint()));
        jmlIntMap.put(GT, new TypedOperator(intKjt, intLDT.getGreaterThan()));
        jmlIntMap.put(LT, new TypedOperator(intKjt, intLDT.getLessThan()));
        jmlIntMap.put(GTE, new TypedOperator(intKjt, intLDT.getGreaterOrEquals()));
        jmlIntMap.put(LTE, new TypedOperator(intKjt, intLDT.getLessOrEquals()));

        jmlCheckedIntMap.put(ADD, new TypedOperator(intKjt, intLDT.getCheckedAddInt()));
        jmlCheckedIntMap.put(SUBTRACT, new TypedOperator(intKjt, intLDT.getCheckedSubInt()));
        jmlCheckedIntMap.put(MULT, new TypedOperator(intKjt, intLDT.getCheckedMulInt()));
        jmlCheckedIntMap.put(DIVISION, new TypedOperator(intKjt, intLDT.getCheckedDivInt()));
        jmlCheckedIntMap.put(BITWISE_AND,
            new TypedOperator(intKjt, intLDT.getCheckedBitwiseAndInt()));
        jmlCheckedIntMap.put(BITWISE_OR,
            new TypedOperator(intKjt, intLDT.getCheckedBitwiseOrInt()));
        jmlCheckedIntMap.put(BITWISE_XOR,
            new TypedOperator(intKjt, intLDT.getCheckedBitwiseXOrInt()));
        jmlCheckedIntMap.put(SHIFT_RIGHT,
            new TypedOperator(intKjt, intLDT.getCheckedShiftRightInt()));
        jmlCheckedIntMap.put(SHIFT_LEFT,
            new TypedOperator(intKjt, intLDT.getCheckedShiftLeftInt()));
        jmlCheckedIntMap.put(UNSIGNED_SHIFT_RIGHT,
            new TypedOperator(intKjt, intLDT.getCheckedUnsignedShiftRightInt()));
        jmlCheckedIntMap.put(BITWISE_NEGATE,
            new TypedOperator(intKjt, intLDT.getCheckedBitwiseNegateInt()));
        jmlCheckedIntMap.put(UNARY_MINUS,
            new TypedOperator(intKjt, intLDT.getCheckedUnaryMinusInt()));
        jmlCheckedIntMap.put(GT, new TypedOperator(intKjt, intLDT.getGreaterThan()));
        jmlCheckedIntMap.put(LT, new TypedOperator(intKjt, intLDT.getLessThan()));
        jmlCheckedIntMap.put(GTE, new TypedOperator(intKjt, intLDT.getGreaterOrEquals()));
        jmlCheckedIntMap.put(LTE, new TypedOperator(intKjt, intLDT.getLessOrEquals()));

        Map<JMLOperator, TypedOperator> jmlLongMap = new EnumMap<>(JMLOperator.class);
        jmlLongMap.put(ADD, new TypedOperator(longKjt, intLDT.getAddJlong()));
        jmlLongMap.put(SUBTRACT, new TypedOperator(longKjt, intLDT.getSubJlong()));
        jmlLongMap.put(MULT, new TypedOperator(longKjt, intLDT.getMulJlong()));
        jmlLongMap.put(DIVISION, new TypedOperator(longKjt, intLDT.getDivJlong()));
        jmlLongMap.put(MODULO, new TypedOperator(longKjt, intLDT.getModJlong()));
        jmlLongMap.put(BITWISE_AND, new TypedOperator(longKjt, intLDT.getBitwiseAndJLong()));
        jmlLongMap.put(BITWISE_OR, new TypedOperator(longKjt, intLDT.getBitwiseOrJlong()));
        jmlLongMap.put(BITWISE_XOR, new TypedOperator(longKjt, intLDT.getXorJlong()));
        jmlLongMap.put(SHIFT_RIGHT, new TypedOperator(longKjt, intLDT.getShiftrightJlong()));
        jmlLongMap.put(SHIFT_LEFT, new TypedOperator(longKjt, intLDT.getShiftleftJlong()));
        jmlLongMap.put(UNSIGNED_SHIFT_RIGHT,
            new TypedOperator(longKjt, intLDT.getUnsignedshiftrightJlong()));
        jmlLongMap.put(BITWISE_NEGATE, new TypedOperator(longKjt, intLDT.getBitwiseNegateJlong()));
        jmlLongMap.put(UNARY_MINUS, new TypedOperator(longKjt, intLDT.getUnaryMinusJlong()));
        jmlLongMap.put(GT, new TypedOperator(longKjt, intLDT.getGreaterThan()));
        jmlLongMap.put(LT, new TypedOperator(longKjt, intLDT.getLessThan()));
        jmlLongMap.put(GTE, new TypedOperator(longKjt, intLDT.getGreaterOrEquals()));
        jmlLongMap.put(LTE, new TypedOperator(longKjt, intLDT.getLessOrEquals()));

        jmlCheckedLongMap.put(ADD, new TypedOperator(longKjt, intLDT.getCheckedAddLong()));
        jmlCheckedLongMap.put(SUBTRACT, new TypedOperator(longKjt, intLDT.getCheckedSubLong()));
        jmlCheckedLongMap.put(MULT, new TypedOperator(longKjt, intLDT.getCheckedMulLong()));
        jmlCheckedLongMap.put(DIVISION, new TypedOperator(longKjt, intLDT.getCheckedDivLong()));
        jmlCheckedLongMap.put(BITWISE_AND,
            new TypedOperator(longKjt, intLDT.getCheckedBitwiseAndLong()));
        jmlCheckedLongMap.put(BITWISE_OR,
            new TypedOperator(longKjt, intLDT.getCheckedBitwiseOrLong()));
        jmlCheckedLongMap.put(BITWISE_XOR,
            new TypedOperator(longKjt, intLDT.getCheckedBitwiseXOrLong()));
        jmlCheckedLongMap.put(SHIFT_RIGHT,
            new TypedOperator(longKjt, intLDT.getCheckedShiftRightLong()));
        jmlCheckedLongMap.put(SHIFT_LEFT,
            new TypedOperator(longKjt, intLDT.getCheckedShiftLeftLong()));
        jmlCheckedLongMap.put(UNSIGNED_SHIFT_RIGHT,
            new TypedOperator(longKjt, intLDT.getCheckedUnsignedShiftRightLong()));
        jmlCheckedLongMap.put(BITWISE_NEGATE,
            new TypedOperator(longKjt, intLDT.getCheckedBitwiseNegateLong()));
        jmlCheckedLongMap.put(UNARY_MINUS,
            new TypedOperator(longKjt, intLDT.getCheckedUnaryMinusLong()));
        jmlCheckedLongMap.put(GT, new TypedOperator(longKjt, intLDT.getGreaterThan()));
        jmlCheckedLongMap.put(LT, new TypedOperator(longKjt, intLDT.getLessThan()));
        jmlCheckedLongMap.put(GTE, new TypedOperator(longKjt, intLDT.getGreaterOrEquals()));
        jmlCheckedLongMap.put(LTE, new TypedOperator(longKjt, intLDT.getLessOrEquals()));

        jmlBigintMap.put(ADD, new TypedOperator(bigIntKjt, intLDT.getAdd()));
        jmlBigintMap.put(SUBTRACT, new TypedOperator(bigIntKjt, intLDT.getSub()));
        jmlBigintMap.put(MULT, new TypedOperator(bigIntKjt, intLDT.getMul()));
        jmlBigintMap.put(DIVISION, new TypedOperator(bigIntKjt, intLDT.getJDivision()));
        jmlBigintMap.put(MODULO, new TypedOperator(bigIntKjt, intLDT.getJModulo()));
        jmlBigintMap.put(BITWISE_AND, new TypedOperator(bigIntKjt, intLDT.getBinaryAnd()));
        jmlBigintMap.put(BITWISE_OR, new TypedOperator(bigIntKjt, intLDT.getBinaryOr()));
        jmlBigintMap.put(BITWISE_XOR, new TypedOperator(bigIntKjt, intLDT.getBinaryXOr()));
        jmlBigintMap.put(SHIFT_RIGHT, new TypedOperator(bigIntKjt, intLDT.getShiftright()));
        jmlBigintMap.put(SHIFT_LEFT, new TypedOperator(bigIntKjt, intLDT.getShiftleft()));
        // jmlBigintMap.put(new TypedOperator(bigIntKjt, UNSIGNED_SHIFT_RIGHT,
        // intLDT.getUnsignedshiftrightJlong()));
        // jmlBigintMap.put(new TypedOperator(bigIntKjt, BITWISE_NEGATE,
        // intLDT.getBitwiseNegate()));
        jmlBigintMap.put(UNARY_MINUS, new TypedOperator(bigIntKjt, intLDT.getNeg()));
        jmlBigintMap.put(GT, new TypedOperator(bigIntKjt, intLDT.getGreaterThan()));
        jmlBigintMap.put(LT, new TypedOperator(bigIntKjt, intLDT.getLessThan()));
        jmlBigintMap.put(GTE, new TypedOperator(bigIntKjt, intLDT.getGreaterOrEquals()));
        jmlBigintMap.put(LTE, new TypedOperator(bigIntKjt, intLDT.getLessOrEquals()));

        opCategories.put(PrimitiveType.JAVA_BIGINT, jmlBigintMap);
        opCategories.put(PrimitiveType.JAVA_INT, jmlIntMap);
        opCategories.put(PrimitiveType.JAVA_LONG, jmlLongMap);
    }

    public SpecMathMode replaceSpecMathMode(SpecMathMode specMathMode) {
        var mode = this.specMathMode;
        this.specMathMode = specMathMode;
        return mode;
    }

    public SpecMathMode getSpecMathMode() {
        return this.specMathMode;
    }

    @Override
    protected @Nullable TypedOperator getOperator(Type promotedType, JMLOperator op) {
        if (specMathMode == SpecMathMode.JAVA) {
            return LDTHandler.getOperatorFromMap(opCategories.get(promotedType), op);
        }

        var isIntLike = PrimitiveType.JAVA_INT.equals(promotedType)
                || PrimitiveType.JAVA_LONG.equals(promotedType)
                || PrimitiveType.JAVA_BIGINT.equals(promotedType);
        if (!isIntLike) {
            return null;
        }

        if (this.specMathMode == SpecMathMode.BIGINT) {
            // Always use bigint operator
            return jmlBigintMap.get(op);
        }

        if (PrimitiveType.JAVA_BIGINT.equals(promotedType)) {
            return jmlBigintMap.get(op);
        } else if (PrimitiveType.JAVA_LONG.equals(promotedType)) {
            return jmlCheckedLongMap.get(op);
        } else {
            return jmlCheckedIntMap.get(op);
        }
    }
}
