/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import java.util.HashMap;
import java.util.LinkedHashMap;

import de.uka.ilkd.key.java.ConvertException;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.ServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.abstraction.Type;
import recoder.java.declaration.TypeDeclaration;
import recoder.kit.UnitKit;
import recoder.service.DefaultNameInfo;



/**
 * This is a specialisation of the NameInfo interface which allows KeY to detect multiple
 * declaration of types. It stores all defined type (w/o possible some array types which do not
 * matter) in a hash table to look up.
 *
 * If it records an attempt to register a declaration type twice, a verbose conversion exception is
 * thrown.
 *
 * It also reports a missing "java.lang.Object" definition in a {@link ConvertException}. Recoder
 * itself usually fails at a random point with a {@link NullPointerException}.
 *
 * An instance of this class is created in {@link KeYCrossReferenceServiceConfiguration}.
 *
 * @author MU
 *
 */
public class KeYCrossReferenceNameInfo extends DefaultNameInfo {
    private static final Logger LOGGER = LoggerFactory.getLogger(KeYCrossReferenceNameInfo.class);

    // this somewhat doubles name2type in DefaultNameInfo to which we have no access
    private final HashMap<String, ClassType> classtypes = new LinkedHashMap<>();

    public KeYCrossReferenceNameInfo(ServiceConfiguration config) {
        super(config);
    }

    /**
     * register a class type.
     *
     * @param ct class type to register
     * @throws ConvertException if there was already a different type registered for the same name
     */
    @Override
    public void register(ClassType ct) {

        String name = ct.getFullName();
        ClassType old = classtypes.get(name);
        if (old != null && ct != old) {
            String d1, d2;
            if (ct instanceof TypeDeclaration) {
                d1 = UnitKit.getCompilationUnit((TypeDeclaration) ct).getOriginalDataLocation()
                        .toString();
            } else {
                d1 = ct.toString();
            }
            if (old instanceof TypeDeclaration) {
                d2 = UnitKit.getCompilationUnit((TypeDeclaration) old).getOriginalDataLocation()
                        .toString();
            } else {
                d2 = old.toString();
            }
            LOGGER.warn(
                "Datatype {} declared twice: Once in {} and once in {}, Keeping one from {}", name,
                d1, d2, d2);
            return;
        }

        super.register(ct);

        classtypes.put(name, ct);
    }

    /**
     * unregister a class type. This happens for instance when removing an EnumDeclaration and
     * inserting an EnumClassDeclaration instead
     *
     * @param fullname name of the type to be unregistered
     */
    @Override
    public void unregisterClassType(String fullname) {
        super.unregisterClassType(fullname);
        classtypes.remove(fullname);
    }

    /*
     * just to make sure that classtypes captures all non-array types.
     */
    @Override
    public Type getType(String name) {
        Type t = super.getType(name);
        if (t instanceof ClassType) {
            classtypes.put(name, (ClassType) t);
        }
        return t;
    }

    /**
     * {@inheritDoc}
     *
     * This implementation checks whether an implementation is available and fails if not.
     *
     * @throws ConvertException if no implementation of java.lang.Object is available presently.
     */
    @Override
    public ClassType getJavaLangObject() throws ConvertException {
        ClassType result = super.getJavaLangObject();
        if (result == null) {
            throw new ConvertException("Class type 'java.lang.Object' cannot be found");
        }
        return result;
    }

}
