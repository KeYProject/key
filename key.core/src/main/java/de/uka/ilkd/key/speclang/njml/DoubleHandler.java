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
import de.uka.ilkd.key.ldt.DoubleLDT;
import de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator;

import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.*;

public class DoubleHandler extends LDTHandler {

    private final Map<JMLOperator, TypedOperator> opMap = new EnumMap<>(JMLOperator.class);

    public DoubleHandler(Services services) {
        super(services);

        DoubleLDT doubleLDT = services.getTypeConverter().getDoubleLDT();
        KeYJavaType doubleKjt = services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_DOUBLE);

        opMap.put(ADD, new TypedOperator(doubleKjt, doubleLDT.getAdd()));
        opMap.put(SUBTRACT, new TypedOperator(doubleKjt, doubleLDT.getSub()));
        opMap.put(MULT, new TypedOperator(doubleKjt, doubleLDT.getMul()));
        opMap.put(DIVISION, new TypedOperator(doubleKjt, doubleLDT.getDiv()));
        opMap.put(MODULO, new TypedOperator(doubleKjt, doubleLDT.getJavaMod()));
        opMap.put(UNARY_MINUS, new TypedOperator(doubleKjt, doubleLDT.getNeg()));
        opMap.put(GT, new TypedOperator(doubleKjt, doubleLDT.getGreaterThan()));
        opMap.put(LT, new TypedOperator(doubleKjt, doubleLDT.getLessThan()));
        opMap.put(GTE, new TypedOperator(doubleKjt, doubleLDT.getGreaterOrEquals()));
        opMap.put(LTE, new TypedOperator(doubleKjt, doubleLDT.getLessOrEquals()));
    }

    @Override
    protected @Nullable TypedOperator getOperator(Type promotedType, JMLOperator op) {
        if (promotedType.equals(PrimitiveType.JAVA_DOUBLE)) {
            return LDTHandler.getOperatorFromMap(this.opMap, op);
        } else {
            return null;
        }
    }
}
