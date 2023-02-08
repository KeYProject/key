/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
// This file is part of the RECODER library and protected by the LGPL.

package recoder.abstraction;

import java.util.List;

/**
 * A program model element representing fields.
 *
 * @author AL
 * @author RN
 * @author TG
 */
public interface Field extends Variable, Member {
    List<? extends TypeArgument> getTypeArguments();
}
