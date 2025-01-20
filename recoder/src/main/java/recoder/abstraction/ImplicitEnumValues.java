/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
