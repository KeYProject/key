package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.ldt.DoubleLDT;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator;

import java.util.EnumMap;
import java.util.Map;

import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.*;

public class DoubleHandler extends LDTHandler {

    private final Map<JMLOperator, Operator> opMap = new EnumMap<>(JMLOperator.class);

    public DoubleHandler(Services services) {
        super(services);

        DoubleLDT doubleLDT = services.getTypeConverter().getDoubleLDT();

        opMap.put(ADD, doubleLDT.getAdd());
        opMap.put(SUBTRACT, doubleLDT.getSub());
        opMap.put(MULT, doubleLDT.getMul());
        opMap.put(DIVISION, doubleLDT.getDiv());
        opMap.put(MODULO, doubleLDT.getJavaMod());
        opMap.put(UNARY_MINUS, doubleLDT.getNeg());
        opMap.put(GT, doubleLDT.getGreaterThan());
        opMap.put(LT, doubleLDT.getLessThan());
        opMap.put(GTE, doubleLDT.getGreaterOrEquals());
        opMap.put(LTE, doubleLDT.getLessOrEquals());
    }

    @Override
    protected Map<JMLOperator, Operator> getOperatorMap(Type promotedType) {
        if (promotedType == PrimitiveType.JAVA_DOUBLE) {
            return opMap;
        } else {
            return null;
        }
    }

}
