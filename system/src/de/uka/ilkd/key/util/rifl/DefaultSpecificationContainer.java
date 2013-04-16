package de.uka.ilkd.key.util.rifl;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.util.rifl.SpecificationEntity.Field;
import de.uka.ilkd.key.util.rifl.SpecificationEntity.Parameter;
import de.uka.ilkd.key.util.rifl.SpecificationEntity.ReturnValue;

/** Default implementation of {@link SpecificationContainer}.
 * @author bruns
 */
public class DefaultSpecificationContainer implements SpecificationContainer {
    
    private Map<Field,String> field2domain = new HashMap<Field, String>();
    private Map<Parameter,String> param2domain  = new HashMap<Parameter, String>();
    private Map<ReturnValue,String> return2domain  = new HashMap<ReturnValue, String>();

    public DefaultSpecificationContainer(Map<SpecificationEntity,String> domainAssignments) {
        for (Entry<SpecificationEntity, String> e: domainAssignments.entrySet()) {
            if (e.getKey() instanceof Field)
                field2domain.put((Field) e.getKey(), e.getValue());
            else if (e.getKey() instanceof Parameter)
                param2domain.put((Parameter) e.getKey(), e.getValue());
            else if (e.getKey() instanceof ReturnValue)
                return2domain.put((ReturnValue) e.getKey(), e.getValue());
        }
    }

    @Override
    public String returnValue(String inPackage, String inClass,
            String methodName, String[] paramTypes) {
        return return2domain.get(new ReturnValue(methodName, paramTypes, inPackage, inClass));
    }

    @Override
    public String returnValue(recoder.java.declaration.MethodDeclaration md) {
        final recoder.abstraction.ClassType ctype = md.getContainingClassType();
        return returnValue(ctype.getPackage().getFullName(), 
                ctype.getName(), md.getName(), extractParamTypes(md));
    }

    @Override
    public String parameter(String inPackage, String inClass,
            String methodName, String[] paramTypes, int index) {
        return param2domain.get(new Parameter(index, methodName, paramTypes, inPackage, inClass));
    }

    @Override
    public String parameter(recoder.java.declaration.MethodDeclaration md, int index) {
        String[] paramTypes = extractParamTypes(md);
        final recoder.abstraction.ClassType ctype = md.getContainingClassType();
        return parameter(ctype.getPackage().getFullName(), 
                ctype.getName(), md.getName(), paramTypes, index);
    }

    private String[] extractParamTypes(recoder.java.declaration.MethodDeclaration md) {
        final int params = md.getParameterDeclarationCount();
        final String[] paramTypes = new String[params];
        for (int i= 0; i < params; i++) {
            final recoder.java.declaration.ParameterDeclaration pd = 
                    md.getParameterDeclarationAt(i);
            paramTypes[i] = pd.getTypeReference().getName();
        }
        return paramTypes;
    }

    @Override
    public String field(String inPackage, String inClass, String name) {
        return field2domain.get(new Field(name, inPackage, inClass));
    }

    @Override
    public String field(recoder.java.declaration.FieldDeclaration fd) {
        recoder.java.declaration.FieldSpecification fs = fd.getVariables().get(0);
        String inClass = fs.getContainingClassType().getName();
        String inPackage = fs.getContainingClassType().getPackage().getFullName();
        return field(inPackage, inClass, fs.getName());
    }

}
