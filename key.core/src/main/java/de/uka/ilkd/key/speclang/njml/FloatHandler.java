/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.speclang.njml;

import java.util.EnumMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.ldt.FloatLDT;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator;

import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.ADD;
import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.DIVISION;
import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.GT;
import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.GTE;
import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.LT;
import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.LTE;
import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.MODULO;
import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.MULT;
import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.SUBTRACT;
import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.UNARY_MINUS;

public class FloatHandler extends LDTHandler {

    private final Map<JMLOperator, Operator> opMap =
        new EnumMap<>(JMLOperator.class);

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
    protected Map<JMLOperator, Operator> getOperatorMap(Type promotedType) {
        if (promotedType == PrimitiveType.JAVA_FLOAT) {
            return opMap;
        } else {
            return null;
        }
    }

}
