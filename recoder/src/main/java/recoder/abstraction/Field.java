/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
