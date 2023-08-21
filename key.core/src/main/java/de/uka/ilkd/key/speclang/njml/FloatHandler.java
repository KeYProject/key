/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.util.EnumMap;
import java.util.Map;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.ldt.FloatLDT;
import de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator;

import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.*;

public class FloatHandler extends LDTHandler {

    private final Map<JMLOperator, TypedOperator> opMap = new EnumMap<>(JMLOperator.class);

    public FloatHandler(Services services) {
        super(services);

        FloatLDT floatLDT = services.getTypeConverter().getFloatLDT();
        KeYJavaType floatKjt = services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_FLOAT);

        opMap.put(ADD, new TypedOperator(floatKjt, floatLDT.getAdd()));
        opMap.put(SUBTRACT, new TypedOperator(floatKjt, floatLDT.getSub()));
        opMap.put(MULT, new TypedOperator(floatKjt, floatLDT.getMul()));
        opMap.put(DIVISION, new TypedOperator(floatKjt, floatLDT.getDiv()));
        opMap.put(MODULO, new TypedOperator(floatKjt, floatLDT.getJavaMod()));
        opMap.put(UNARY_MINUS, new TypedOperator(floatKjt, floatLDT.getNeg()));
        opMap.put(GT, new TypedOperator(floatKjt, floatLDT.getGreaterThan()));
        opMap.put(LT, new TypedOperator(floatKjt, floatLDT.getLessThan()));
        opMap.put(GTE, new TypedOperator(floatKjt, floatLDT.getGreaterOrEquals()));
        opMap.put(LTE, new TypedOperator(floatKjt, floatLDT.getLessOrEquals()));
    }

    @Override
    protected @Nullable TypedOperator getOperator(Type promotedType, JMLOperator op) {
        if (promotedType.equals(PrimitiveType.JAVA_FLOAT)) {
            return LDTHandler.getOperatorFromMap(this.opMap, op);
        } else {
            return null;
        }
    }
}
