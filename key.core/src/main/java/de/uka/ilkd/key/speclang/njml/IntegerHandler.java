package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator;

import java.util.EnumMap;
import java.util.IdentityHashMap;
import java.util.Map;

import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.*;

public class IntegerHandler extends LDTHandler {

    private final Map<JMLOperator, Operator> jmlIntMap = new EnumMap<>(JMLOperator.class);

    private final Map<JMLOperator, Operator> jmlLongMap = new EnumMap<>(JMLOperator.class);

    private final Map<JMLOperator, Operator> jmlBigintMap = new EnumMap<>(JMLOperator.class);

    private final Map<PrimitiveType, Map<JMLOperator, Operator>> opCategories =
        new IdentityHashMap<>();

    private final Services services;

    public IntegerHandler(Services services) {
        super(services);
        this.services = services;

        IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();
        jmlIntMap.put(ADD, intLDT.getJavaAddInt());
        jmlIntMap.put(SUBTRACT, intLDT.getJavaSubInt());
        jmlIntMap.put(MULT, intLDT.getJavaMulInt());
        jmlIntMap.put(DIVISION, intLDT.getJavaDivInt());
        jmlIntMap.put(MODULO, intLDT.getJavaMod());
        jmlIntMap.put(BITWISE_AND, intLDT.getJavaBitwiseAndInt());
        jmlIntMap.put(BITWISE_OR, intLDT.getJavaBitwiseOrInt());
        jmlIntMap.put(BITWISE_XOR, intLDT.getJavaBitwiseXOrInt());
        jmlIntMap.put(SHIFT_RIGHT, intLDT.getJavaShiftRightInt());
        jmlIntMap.put(SHIFT_LEFT, intLDT.getJavaShiftLeftInt());
        jmlIntMap.put(UNSIGNED_SHIFT_RIGHT, intLDT.getJavaUnsignedShiftRightInt());
        jmlIntMap.put(BITWISE_NEGATE, intLDT.getJavaBitwiseNegation());
        jmlIntMap.put(UNARY_MINUS, intLDT.getJavaUnaryMinusInt());
        jmlIntMap.put(GT, intLDT.getGreaterThan());
        jmlIntMap.put(LT, intLDT.getLessThan());
        jmlIntMap.put(GTE, intLDT.getGreaterOrEquals());
        jmlIntMap.put(LTE, intLDT.getLessOrEquals());

        jmlLongMap.put(ADD, intLDT.getJavaAddLong());
        jmlLongMap.put(SUBTRACT, intLDT.getJavaSubLong());
        jmlLongMap.put(MULT, intLDT.getJavaMulLong());
        jmlLongMap.put(DIVISION, intLDT.getJavaDivLong());
        jmlLongMap.put(MODULO, intLDT.getJavaMod());
        jmlLongMap.put(BITWISE_AND, intLDT.getJavaBitwiseAndLong());
        jmlLongMap.put(BITWISE_OR, intLDT.getJavaBitwiseOrLong());
        jmlLongMap.put(BITWISE_XOR, intLDT.getJavaBitwiseXOrLong());
        jmlLongMap.put(SHIFT_RIGHT, intLDT.getJavaShiftRightLong());
        jmlLongMap.put(SHIFT_LEFT, intLDT.getJavaShiftLeftLong());
        jmlLongMap.put(UNSIGNED_SHIFT_RIGHT, intLDT.getJavaUnsignedShiftRightLong());
        jmlLongMap.put(BITWISE_NEGATE, intLDT.getJavaBitwiseNegation());
        jmlLongMap.put(UNARY_MINUS, intLDT.getJavaUnaryMinusLong());
        jmlLongMap.put(GT, intLDT.getGreaterThan());
        jmlLongMap.put(LT, intLDT.getLessThan());
        jmlLongMap.put(GTE, intLDT.getGreaterOrEquals());
        jmlLongMap.put(LTE, intLDT.getLessOrEquals());

        jmlBigintMap.put(ADD, intLDT.getAdd());
        jmlBigintMap.put(SUBTRACT, intLDT.getSub());
        jmlBigintMap.put(MULT, intLDT.getMul());
        jmlBigintMap.put(DIVISION, intLDT.getJDivision());
        jmlBigintMap.put(MODULO, intLDT.getJavaMod());
        jmlBigintMap.put(UNARY_MINUS, intLDT.getNeg());
        jmlBigintMap.put(GT, intLDT.getGreaterThan());
        jmlBigintMap.put(LT, intLDT.getLessThan());
        jmlBigintMap.put(GTE, intLDT.getGreaterOrEquals());
        jmlBigintMap.put(LTE, intLDT.getLessOrEquals());

        opCategories.put(PrimitiveType.JAVA_BIGINT, jmlBigintMap);
        opCategories.put(PrimitiveType.JAVA_INT, jmlIntMap);
        opCategories.put(PrimitiveType.JAVA_LONG, jmlLongMap);
    }

    @Override
    protected Map<JMLOperator, Operator> getOperatorMap(Type promotedType) {
        Map<JMLOperator, Operator> opMap = opCategories.get(promotedType);
        return opMap;
    }

}
