package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator;

import javax.annotation.Nullable;
import java.util.EnumMap;
import java.util.IdentityHashMap;
import java.util.Map;

import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.*;

public class IntegerHandler extends LDTHandler {

    private final Map<JMLOperator, Operator> jmlIntMap = new EnumMap<>(JMLOperator.class);
    private final Map<JMLOperator, Operator> jmlCheckedIntMap = new EnumMap<>(JMLOperator.class);

    private final Map<JMLOperator, Operator> jmlLongMap = new EnumMap<>(JMLOperator.class);
    private final Map<JMLOperator, Operator> jmlCheckedLongMap = new EnumMap<>(JMLOperator.class);

    private final Map<JMLOperator, Operator> jmlBigintMap = new EnumMap<>(JMLOperator.class);

    private final Map<Type, Map<JMLOperator, Operator>> opCategories = new IdentityHashMap<>();

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

        IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();
        jmlIntMap.put(ADD, intLDT.getAddJint());
        jmlIntMap.put(SUBTRACT, intLDT.getSubJint());
        jmlIntMap.put(MULT, intLDT.getMulJint());
        jmlIntMap.put(DIVISION, intLDT.getDivJint());
        jmlIntMap.put(MODULO, intLDT.getModJint());
        jmlIntMap.put(BITWISE_AND, intLDT.getBitwiseAndJInt());
        jmlIntMap.put(BITWISE_OR, intLDT.getBitwiseOrJInt());
        jmlIntMap.put(BITWISE_XOR, intLDT.getXorJint());
        jmlIntMap.put(SHIFT_RIGHT, intLDT.getShiftrightJint());
        jmlIntMap.put(SHIFT_LEFT, intLDT.getShiftleftJint());
        jmlIntMap.put(UNSIGNED_SHIFT_RIGHT, intLDT.getUnsignedshiftrightJint());
        // jmlIntMap.put(BITWISE_NEGATE, intLDT.getBitwiseNegateJint());
        jmlIntMap.put(UNARY_MINUS, intLDT.getUnaryMinusJint());
        jmlIntMap.put(GT, intLDT.getGreaterThan());
        jmlIntMap.put(LT, intLDT.getLessThan());
        jmlIntMap.put(GTE, intLDT.getGreaterOrEquals());
        jmlIntMap.put(LTE, intLDT.getLessOrEquals());

        jmlCheckedIntMap.put(ADD, intLDT.getCheckedAddInt());
        jmlCheckedIntMap.put(SUBTRACT, intLDT.getCheckedSubInt());
        jmlCheckedIntMap.put(MULT, intLDT.getCheckedMulInt());
        jmlCheckedIntMap.put(DIVISION, intLDT.getCheckedDivInt());
        jmlCheckedIntMap.put(BITWISE_AND, intLDT.getCheckedBitwiseAndInt());
        jmlCheckedIntMap.put(BITWISE_OR, intLDT.getCheckedBitwiseOrInt());
        jmlCheckedIntMap.put(BITWISE_XOR, intLDT.getCheckedBitwiseXOrInt());
        jmlCheckedIntMap.put(SHIFT_RIGHT, intLDT.getCheckedShiftRightInt());
        jmlCheckedIntMap.put(SHIFT_LEFT, intLDT.getCheckedShiftLeftInt());
        jmlCheckedIntMap.put(UNSIGNED_SHIFT_RIGHT, intLDT.getCheckedUnsignedShiftRightInt());
        // jmlCheckedIntMap.put(BITWISE_NEGATE, inCheckedtLDT.getBitwiseNegateInt());
        jmlCheckedIntMap.put(UNARY_MINUS, intLDT.getCheckedUnaryMinusInt());
        jmlCheckedIntMap.put(GT, intLDT.getGreaterThan());
        jmlCheckedIntMap.put(LT, intLDT.getLessThan());
        jmlCheckedIntMap.put(GTE, intLDT.getGreaterOrEquals());
        jmlCheckedIntMap.put(LTE, intLDT.getLessOrEquals());

        jmlLongMap.put(ADD, intLDT.getAddJlong());
        jmlLongMap.put(SUBTRACT, intLDT.getSubJlong());
        jmlLongMap.put(MULT, intLDT.getMulJlong());
        jmlLongMap.put(DIVISION, intLDT.getDivJlong());
        jmlLongMap.put(MODULO, intLDT.getModJlong());
        jmlLongMap.put(BITWISE_AND, intLDT.getBitwiseAndJLong());
        jmlLongMap.put(BITWISE_OR, intLDT.getBitwiseOrJlong());
        jmlLongMap.put(BITWISE_XOR, intLDT.getXorJlong());
        jmlLongMap.put(SHIFT_RIGHT, intLDT.getShiftrightJlong());
        jmlLongMap.put(SHIFT_LEFT, intLDT.getShiftleftJlong());
        jmlLongMap.put(UNSIGNED_SHIFT_RIGHT, intLDT.getUnsignedshiftrightJlong());
        // jmlLongMap.put(BITWISE_NEGATE, intLDT.getBitwiseNegateJlong());
        jmlLongMap.put(UNARY_MINUS, intLDT.getUnaryMinusJlong());
        jmlLongMap.put(GT, intLDT.getGreaterThan());
        jmlLongMap.put(LT, intLDT.getLessThan());
        jmlLongMap.put(GTE, intLDT.getGreaterOrEquals());
        jmlLongMap.put(LTE, intLDT.getLessOrEquals());

        jmlCheckedLongMap.put(ADD, intLDT.getCheckedAddLong());
        jmlCheckedLongMap.put(SUBTRACT, intLDT.getCheckedSubLong());
        jmlCheckedLongMap.put(MULT, intLDT.getCheckedMulLong());
        jmlCheckedLongMap.put(DIVISION, intLDT.getCheckedDivLong());
        jmlCheckedLongMap.put(BITWISE_AND, intLDT.getCheckedBitwiseAndLong());
        jmlCheckedLongMap.put(BITWISE_OR, intLDT.getCheckedBitwiseOrLong());
        jmlCheckedLongMap.put(BITWISE_XOR, intLDT.getCheckedBitwiseXOrLong());
        jmlCheckedLongMap.put(SHIFT_RIGHT, intLDT.getCheckedShiftRightLong());
        jmlCheckedLongMap.put(SHIFT_LEFT, intLDT.getCheckedShiftLeftLong());
        jmlCheckedLongMap.put(UNSIGNED_SHIFT_RIGHT, intLDT.getCheckedUnsignedShiftRightLong());
        // jmlCheckedLongMap.put(BITWISE_NEGATE, inCheckedtLDT.getBitwiseNegateLong());
        jmlCheckedLongMap.put(UNARY_MINUS, intLDT.getCheckedUnaryMinusLong());
        jmlCheckedLongMap.put(GT, intLDT.getGreaterThan());
        jmlCheckedLongMap.put(LT, intLDT.getLessThan());
        jmlCheckedLongMap.put(GTE, intLDT.getGreaterOrEquals());
        jmlCheckedLongMap.put(LTE, intLDT.getLessOrEquals());

        jmlBigintMap.put(ADD, intLDT.getAdd());
        jmlBigintMap.put(SUBTRACT, intLDT.getSub());
        jmlBigintMap.put(MULT, intLDT.getMul());
        jmlBigintMap.put(DIVISION, intLDT.getJDivision());
        jmlBigintMap.put(MODULO, intLDT.getJModulo());
        jmlBigintMap.put(BITWISE_AND, intLDT.getBinaryAnd());
        jmlBigintMap.put(BITWISE_OR, intLDT.getBinaryOr());
        jmlBigintMap.put(BITWISE_XOR, intLDT.getBinaryXOr());
        jmlBigintMap.put(SHIFT_RIGHT, intLDT.getShiftright());
        jmlBigintMap.put(SHIFT_LEFT, intLDT.getShiftleft());
        // jmlBigintMap.put(UNSIGNED_SHIFT_RIGHT, intLDT.getUnsignedshiftrightJlong());
        // jmlBigintMap.put(BITWISE_NEGATE, intLDT.getBitwiseNegate());
        jmlBigintMap.put(UNARY_MINUS, intLDT.getNeg());
        jmlBigintMap.put(GT, intLDT.getGreaterThan());
        jmlBigintMap.put(LT, intLDT.getLessThan());
        jmlBigintMap.put(GTE, intLDT.getGreaterOrEquals());
        jmlBigintMap.put(LTE, intLDT.getLessOrEquals());


        opCategories.put(PrimitiveType.JAVA_BIGINT, jmlBigintMap);
        opCategories.put(PrimitiveType.JAVA_INT, jmlIntMap);
        opCategories.put(PrimitiveType.JAVA_LONG, jmlLongMap);
    }

    public SpecMathMode replaceSpecMathMode(SpecMathMode specMathMode) {
        var mode = this.specMathMode;
        this.specMathMode = specMathMode;
        return mode;
    }

    @Override
    protected @Nullable Operator getOperator(Type promotedType, JMLOperator op) {
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
