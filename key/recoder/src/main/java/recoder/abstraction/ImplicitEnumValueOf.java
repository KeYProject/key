/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
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
