package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.ldt.FloatLDT;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator;

import javax.annotation.Nullable;
import java.util.EnumMap;
import java.util.Map;

import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.*;

public class FloatHandler extends LDTHandler {

    private final Map<JMLOperator, Operator> opMap = new EnumMap<>(JMLOperator.class);

    public FloatHandler(Services services) {
        super(services);

        FloatLDT floatLDT = services.getTypeConverter().getFloatLDT();

        opMap.put(ADD, floatLDT.getAdd());
        opMap.put(SUBTRACT, floatLDT.getSub());
        opMap.put(MULT, floatLDT.getMul());
        opMap.put(DIVISION, floatLDT.getDiv());
        opMap.put(MODULO, floatLDT.getJavaMod());
        opMap.put(UNARY_MINUS, floatLDT.getNeg());
        opMap.put(GT, floatLDT.getGreaterThan());
        opMap.put(LT, floatLDT.getLessThan());
        opMap.put(GTE, floatLDT.getGreaterOrEquals());
        opMap.put(LTE, floatLDT.getLessOrEquals());
    }

    @Override
    protected @Nullable Operator getOperator(Type promotedType, JMLOperator op) {
        if (promotedType.equals(PrimitiveType.JAVA_FLOAT)) {
            return LDTHandler.getOperatorFromMap(this.opMap, op);
        } else {
            return null;
        }
    }
}
