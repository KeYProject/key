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
public class ImplicitEnumValueOf extends ImplicitEnumMethod {

    /**
     * @param ownerClass
     */
    public ImplicitEnumValueOf(ClassType ownerClass) {
        super(ownerClass);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.NamedModelElement#getName()
     */
    public String getName() {
        return "valueOf";
    }

    public List<? extends TypeParameter> getTypeParameters() {
        return null;
    }

}
