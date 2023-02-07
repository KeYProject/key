/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package recoder.abstraction;

import java.util.List;

/**
 * @author gutzmann
 */
public interface AnnotationUse {
    List<? extends ElementValuePair> getElementValuePairs();
}
