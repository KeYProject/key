/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.rifl;

import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uka.ilkd.key.util.rifl.SpecificationEntity.Field;
import de.uka.ilkd.key.util.rifl.SpecificationEntity.Parameter;
import de.uka.ilkd.key.util.rifl.SpecificationEntity.ReturnValue;
import de.uka.ilkd.key.util.rifl.SpecificationEntity.Type;

/**
 * Default implementation of {@link SpecificationContainer}.
 *
 * @author bruns
 */
public class DefaultSpecificationContainer implements SpecificationContainer {

    private final Map<Field, String> field2domain = new HashMap<>();
    private final Map<Parameter, String> param2domain = new HashMap<>();
    private final Map<ReturnValue, String> return2domain = new HashMap<>();
    private final Set<Entry<String, String>> flow = new LinkedHashSet<>();

    public DefaultSpecificationContainer(Map<SpecificationEntity, String> domainAssignments,
            Set<Entry<String, String>> flow2) {
        // TODO: this copying is ugly and inefficient
        for (final Entry<SpecificationEntity, String> e : domainAssignments.entrySet()) {
            if (e.getKey() instanceof Field) {
                field2domain.put((Field) e.getKey(), e.getValue());
            } else if (e.getKey() instanceof Parameter) {
                param2domain.put((Parameter) e.getKey(), e.getValue());
            } else if (e.getKey() instanceof ReturnValue) {
                return2domain.put((ReturnValue) e.getKey(), e.getValue());
            }
        }
        this.flow.addAll(flow2);
    }

    @Override
    public String toString() {
        return "Fields: " + field2domain + "\nParameters: " + param2domain + "\nReturns: "
            + return2domain + "\nFlows: " + flow;
    }

    private String[] extractParamTypes(recoder.java.declaration.MethodDeclaration md) {
        final int params = md.getParameterDeclarationCount();
        final String[] paramTypes = new String[params];
        for (int i = 0; i < params; i++) {
            final recoder.java.declaration.ParameterDeclaration pd =
                md.getParameterDeclarationAt(i);
            paramTypes[i] = pd.getTypeReference().getName();
        }
        return paramTypes;
    }

    @Override
    public String field(recoder.java.declaration.FieldDeclaration fd, Type type) {
        final recoder.java.declaration.FieldSpecification fs = fd.getVariables().get(0);
        final recoder.abstraction.ClassTypeContainer ctype = fs.getContainingClassType();
        final String inClass = ctype.getName();
        final String inPackage = ctype.getPackage().getFullName();
        return field(inPackage, inClass, fs.getName(), type);
    }

    @Override
    public String field(String inPackage, String inClass, String name, Type type) {
        return field2domain.get(new Field(name, inPackage, inClass, type));
    }

    @Override
    public String parameter(recoder.java.declaration.MethodDeclaration md, int index, Type type) {
        final String[] paramTypes = extractParamTypes(md);
        final recoder.abstraction.ClassType ctype = md.getContainingClassType();
        return parameter(ctype.getPackage().getFullName(), ctype.getName(), md.getName(),
            paramTypes, index, type);
    }

    @Override
    public String parameter(String inPackage, String inClass, String methodName,
            String[] paramTypes, int index, Type type) {
        return param2domain
                .get(new Parameter(index, methodName, paramTypes, inPackage, inClass, type));
    }

    @Override
    public String returnValue(recoder.java.declaration.MethodDeclaration md, Type type) {
        final recoder.abstraction.ClassType ctype = md.getContainingClassType();
        return returnValue(ctype.getPackage().getFullName(), ctype.getName(), md.getName(),
            extractParamTypes(md), type);
    }

    @Override
    public String returnValue(String inPackage, String inClass, String methodName,
            String[] paramTypes, Type type) {
        return return2domain.get(new ReturnValue(methodName, paramTypes, inPackage, inClass, type));
    }

    @Override
    public Set<String> flows(String domain) {
        Set<String> result = new LinkedHashSet<>();
        for (final Entry<String, String> e : flow) {
            if (e.getValue().equals(domain)) {
                result.add(e.getKey());
            }
        }
        return result;
    }
}
