/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
