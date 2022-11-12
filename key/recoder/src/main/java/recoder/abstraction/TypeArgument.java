/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package recoder.abstraction;

import java.util.List;

/**
 * @author Tobias Gutzmann
 */
public interface TypeArgument {
    WildcardMode getWildcardMode();

    String getTypeName();

    List<? extends TypeArgument> getTypeArguments();

    enum WildcardMode {
        None, // Type()
        Any, // ?
        Extends, // ? extends Type()
        Super // ? super Type()
    }
}
