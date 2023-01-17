/*
 * Created on 15.08.2005
 *
 * This file is part of the RECODER library and protected by the LGPL.
 *
 */
package recoder.abstraction;

import java.util.List;

/**
 * @author Tobias Gutzmann
 */
public class ImplicitEnumValues extends ImplicitEnumMethod {

    /**
     * @param ownerClass
     */
    public ImplicitEnumValues(ClassType ownerClass) {
        super(ownerClass);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.NamedModelElement#getName()
     */
    public String getName() {
        return "values";
    }

    public List<? extends TypeParameter> getTypeParameters() {
        return null;
    }

}
