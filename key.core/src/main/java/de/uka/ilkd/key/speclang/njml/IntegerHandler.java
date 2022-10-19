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

    private enum IntType {
        Bigint, Int, Long
    }

    private final Map<JMLOperator, Operator> jmlIntMap = new EnumMap<>(JMLOperator.class);

    private final Map<JMLOperator, Operator> jmlLongMap = new EnumMap<>(JMLOperator.class);

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

        jmlBigintMap.put(ADD, intLDT.getAdd());
        jmlBigintMap.put(SUBTRACT, intLDT.getSub());
        jmlBigintMap.put(MULT, intLDT.getMul());
        jmlBigintMap.put(DIVISION, intLDT.getJDivision());
        jmlBigintMap.put(MODULO, intLDT.getJavaMod());
        // TODO bigint bitwise operators
        // jmlBigintMap.put(BITWISE_AND, intLDT.getBitwiseAndJlong());
        // jmlBigintMap.put(BITWISE_OR, intLDT.getBitwiseOrJlong());
        // jmlBigintMap.put(BITWISE_XOR, intLDT.getXorJlong());
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
        switch (this.specMathMode) {
        case BIGINT: {
            var isIntLike = PrimitiveType.JAVA_INT.equals(promotedType)
                    || PrimitiveType.JAVA_LONG.equals(promotedType)
                    || PrimitiveType.JAVA_BIGINT.equals(promotedType);
            if (!isIntLike) {
                return null;
            }

            // Always use bigint operator
            return jmlBigintMap.get(op);
        }
        case JAVA:
            return LDTHandler.getOperatorFromMap(opCategories.get(promotedType), op);
        }

        throw new AssertionError("unreachable");
    }
}
